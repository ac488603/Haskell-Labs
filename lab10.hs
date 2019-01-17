-- Lab 10: REG closure under other operations

-- Ordinary regular expressions and a show method for them
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE

instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star Empty)  = showString "1"
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"


-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}, and a show instance.
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

evena :: FSM Int
evena = FSM {
  states = [0,1],
  start  = 0,
  finals = [0],
  delta  = [(i, a, d i a) | i <- [0,1], a <- sigma]
  } where d i 'a' = (i + 1) `mod` 2
          d i c   = i

no_aaa :: FSM Int -- accepts any string that doesnt contain aaa
no_aaa  = FSM{
 states = [0..3],
 start  = 0,
 finals = [0..2],
 delta  = [(i, a, d i a) | i <- [0..3], a <- sigma]
}where d i 'a' = min 3 (i + 1)
       d 3 'b' = 3
       d _ 'b' = 0

instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'




-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
-- find the transition given a state q and a letter a
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

--rewritten to to use records
del :: Eq a => FSM a -> a -> Char -> a
del m = ap (delta m)
--rewritten to use records
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . del
--rewritten to use records
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m w = elem (delta_star m (start m) w) (finals m)

toRE :: String -> RE
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


-- Implement each of the following operations on regular expressions or FSMs
--data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE
-- [[reverseRE r]] = rev([[r]]), defined by recursion on r
reverseRE :: RE -> RE
reverseRE Empty = Empty
reverseRE (Letter a)  = Letter a
reverseRE (Union r1 r2) = Union (reverseRE r1) (reverseRE r2)
reverseRE (Cat r1 r2) = Cat (reverseRE r2) (reverseRE r1)
reverseRE (Star r) = Star(reverseRE r)

-- L(complementFSM M) = Sigma^* - L(M)
complementFSM :: Ord a => FSM a -> FSM a
complementFSM m = FSM{
  states = states m,
  start  = start m,
  finals = [q | q<-(states m), (not (elem q (finals m)))],
  delta  = delta m
}

-- L(intersectFSM m1 m2) = L(m1) intersect L(m2)
intersectFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a,b)
intersectFSM m1 m2 = FSM {
  states = (states m1) >< (states m2),
  start  = (start m1, start m2),
  finals = (finals m1) >< (finals m2),
  delta  = [( (q1,q2) , a , ((ap (delta m1) q1 a),(ap (delta m2) q2 a))) | a <-sigma, q1<-(states m1), q2<-(states m2)]
  }

k :: Char -> [Char]
k a = if a == 'a' then "aba." else "bbbaba."

-- [[himage r h]] = h^*([[r]]), defined by recursion on r
himage :: RE -> (Char -> [Char]) -> RE --takes regular expression and a function that takes a character and returns a string
himage Empty h = Empty
himage (Letter a) h = toRE (h a) --take h of a and turn it into a regular expression
himage (Union r1 r2) h = Union (himage r1 h) (himage r2 h)
himage (Cat r1 r2) h = Cat (himage r1 h) (himage r2 h)
himage (Star r) h = Star (himage r h)

h ::Char -> [Char]
h a = if a == 'a' then "bbbb" else "baba"
-- L(hinvimage m h) = (h^*)^{-1}(L(m))
hinvimage :: Ord a => FSM a -> (Char -> [Char]) -> FSM a
hinvimage m h = FSM{
  states = states m,
  start  = start m,
  finals = finals m,
  delta  = [(q, a, (delta_star m q (h a))) | q<-(states m), a <-sigma]
}

-- L(rightq m a) = { w | wa in L(m) }
rightq :: Ord a => FSM a -> Char -> FSM a
rightq m a = FSM{
  states = states m,
  start  = start m,
-- if transition on an 'a' goes to a final state then the final state should be
--the state that the machine it was in before the transition
  finals = [q |(q, b, c)<-(delta m), (b == a), elem c (finals m)],
  delta  = delta m
}

-- Note: left quotient was already implemented in a previous lab
