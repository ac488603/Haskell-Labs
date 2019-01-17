-- Lab 6: FSM constructions for regular operators
--Adam Castillo
-- 108485851
import Data.List (nub, sort, subsequences)


-- Fixed alphabet, but everything below should work for any sigma!
sigma = "abc"

-- Finite state machines indexed by the type of their states
-- M = (states, start, final, transitions)
type FSM a = ([a], a, [a], [(a, Char, a)])


---------------- A solution to Lab 5, ported to FSM a ------------------------

-- no_dups xs = "xs has no duplicates"
no_dups :: Eq a => [a] -> Bool
no_dups [] = True
no_dups (x:xs) = not (elem x xs) && no_dups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

-- func3 as bs ts == "ts determines a function from (as x bs) to cs"
func3 :: (Eq a, Eq b, Eq c) => [a] -> [b] -> [c] -> [(a,b,c)] -> Bool
func3 as bs cs ts = and [single (thirds a b ts) cs | a <- as, b <- bs] where
  thirds a b ts = [c' | (a',b',c') <- ts, a' == a, b' == b]
  single [x] ys = elem x ys
  single _ _ = False

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs &&        -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func3 qs sigma qs d  -- (4)

-- All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

delta :: Eq a => FSM a -> a -> Char -> a
delta (_, _, _, d) = ap d

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(qs, q0, fs, d) w = elem (delta_star m q0 w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, q0, _, _) w = accept2_aux m q0 w

-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = ([0,1], 0, [0], [(i, a, d i a) | i <- [0,1], a <- sigma]) where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = ([0..3], 0, [0..2], [(i, a, d i a) | i <- [0..3], a <- sigma]) where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0


---------------- Some additional useful functions --------------------------

-- Normalize a list, i.e., sort and remove (now adjacent) duplicates.
-- Two lists determine the same set if they normalize to the same list
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the 6 language constructs and test your
-- functions adequately


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0],0,[],[(0,' ',0)])

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0,1,2],0,[1],[(b,c, if c == a && b == 0 then 1 else 2) | c <- sigma, b <- [0..2]])

testlValid = checkFSM(letterFSM 'a')
-- Machine that accepts the language {w} where w in sigma*
-- FSM should have a trap state (1)
-- FSM should also have enough states to process a string (w), total states should be w+1
-- whenever FSM reads a incorrect character it should go to trap state and stay there
-- if in the final state and the machine reads an incorrect character then it should go to trap state
-- if FSM is in state w prelude will cause an exeption,  therfore i can just avoid this exception and just go the the trap state
-- stringFSM "aa",  this machine should have 3 states, 2 for reading the machine and 1 for the trap state
-- (0,a)-> 1,  (0,b) -> 3, (1,a) -> 2, (1,b)-> 3, (2,a) ->3, (2,b)->3, (3,a)->3, (3,b)->3
-- the fs is in this machine is 2
stringFSM :: [Char] -> FSM Int
stringFSM w = ([0..(length w)+1],0,[(length w)],[(j,c,if (j >= length w) || (w !! j /= c) then ((length w)+ 1) else j+1) | j <-[0..(length w)+1], c <- sigma])

teststrValid = checkFSM (stringFSM "aa")

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM m@(qs1, s1, fs1, d1) n@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1,s2)
  fs = [(a,b)|  a <- qs1 , b <- qs2, elem a fs1 || elem b fs2]
  d  = [((a,b),c,((delta m a c),(delta n b c))) |a <- qs1, b <- qs2, c <- sigma]

testuValid = checkFSM (unionFSM (letterFSM 'a') (letterFSM 'b'))
testu1 = accept1 (unionFSM (letterFSM 'a') (letterFSM 'b')) "a"
testu2 = accept1 (unionFSM (letterFSM 'a') (letterFSM 'b')) "b"

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM m@(qs1, s1, fs1, d1) n@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = nub[(q, if (elem q fs1) then (norm (s2:xs)) else (norm xs))| q <- qs1, xs <-(subsequences qs2)]
  s  = (s1,if (elem s1 fs1) then [s2] else [])
  fs = [(q,xs)| (q,xs) <- qs, overlap xs fs2]
  d  = [((q,xs),c,( (delta m q c) , (if (elem (delta m q c) fs1) then (norm (s2:[delta n x c| x <- xs])) else norm([delta n x c| x <- xs])))) | (q,xs) <- qs,c <- sigma]
testcValid = checkFSM (catFSM (stringFSM "aba") (stringFSM "ccc"))
testc1 = accept2 (catFSM (stringFSM "aba") (stringFSM "ccc")) "abaccc"
testc2 = accept2 (catFSM (stringFSM "aba") (starFSM(letterFSM 'c'))) "abaaac"
testc3 = accept2 (catFSM (stringFSM "aba") (starFSM(letterFSM 'c'))) "abacccccc"

correct ::  Ord a => FSM a -> [a] -> [a]
correct m@(qs1, s1, fs1, d1) xs = if (overlap xs fs1) then s1:xs else xs

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM m@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = nub ([]:[ norm(correct m x) |x <- (subsequences qs1)])
  s  = []
  fs = []:[x |x <- qs, overlap x fs1]
  d  = [(xs, c, if xs == [] then norm(correct m [delta m s1 c]) else norm(correct m [delta m x c | x<-xs]))| c <-sigma, xs <- qs]

testsValid =  checkFSM (unionFSM (starFSM (letterFSM 'a')) (starFSM (letterFSM 'b')))
tests1 =  accept1 (unionFSM (starFSM (letterFSM 'a')) (starFSM (letterFSM 'b'))) "c"
tests2 =  accept1 (unionFSM (starFSM (letterFSM 'a')) (starFSM (letterFSM 'b'))) "aaaaa"
tests3 =  accept1 (unionFSM (starFSM (letterFSM 'a')) (starFSM (letterFSM 'b'))) "bbbbb"
tests4 =  accept1 (unionFSM (starFSM (letterFSM 'a')) (starFSM (letterFSM 'b'))) "aaaaab"
tests5 =  accept2 (starFSM (unionFSM (letterFSM 'a')  (letterFSM 'b'))) "ababa" 
-- Bonus Feature (for testing):

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, q0, fs, d) = (qs', q0, fs', d') where
  qs' = sort $ stable $ iterate close ([q0], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = nub $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma
