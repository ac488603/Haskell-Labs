--Adam Castillo
--108485851

-- Lab 8: Non-deterministic finite state machines
-- Feel free to use any additional functions from previous labs

import Data.List (sort, subsequences)
import Control.Monad (replicateM)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Check whether two lists overlap
-- check if element in one list exists in another list
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

evena :: FSM Int
evena = FSM { -- accept string with even amount of as
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

-- Output format for FSMs
instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'


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

---- Lab 8 begins here -----------------------------------------------------

-- Nondeterministic FSMs
--  retirve fields from NFSM
--  nstates m where m is the name of the machine
--  nstarts m
--  nfinals m
--  ndelta  m
data NFSM a = NFSM {
  nstates :: [a],
  nstarts :: [a],
  nfinals :: [a],
  ndelta  :: [(a,Char,a)]
  }

-- my show NFSM
instance Show a => Show (NFSM a) where
    show m = "("   ++ show (nstates m) ++
             ", " ++ show (nstarts m) ++
             ", "  ++ show (nfinals m) ++
             ", [" ++ steps (ndelta m) ++ "])" where
      steps [] = []
      steps [t] = step t
      steps (t:ts) = step t ++ "," ++ steps ts
      step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'

endaab = NFSM{
 nstates = [1..4],
 nstarts = [1],
 nfinals = [4],
 ndelta = [(1,'a',1),(1,'b',1),(1,'a',2),(2,'a',3),(3,'b',4)]
}
ttla = NFSM{
 nstates = [1..4],
 nstarts = [1],
 nfinals = [4],
 ndelta  = [(1,'a',1),(1,'b',1),(1,'a',2),(2,'a',3),(2,'b',3),(3,'a',4),(3,'b',4)]
}
-- nap ts q a == the normalized list of q' such that (q, a, q') is in ts
-- this function is delta for non deterministic finite state machinces
nap :: Ord a => [(a,Char,a)] -> a -> Char -> [a]
nap ts q a = norm [q2 | (q1, a1, q2) <-ts, q1 == q,  a1 == a]

testnap1 =  nap [(1,'a',1),(1,'a',2),(2,'b',4)] 1 'a'
testnap2 =  nap [] 1 'a'


--delta_star from lab 5
--delta_star :: FSM -> Int -> [Char] -> Int
--delta_star m q [] = q
--delta_star m q (w:ws) = delta_star m (delta m q w) ws

-- ndelta_star m q w == normalized list of states m goes to from q on w
-- translated directly from notes (first definition)

--helper function
--union together a list of set
together :: [[a]] -> [a]
together [] = []
together (r:rs)  = r ++ together rs

ndelta_star :: Ord a => NFSM a -> a -> [Char] -> [a]
ndelta_star m q [] = [q]
ndelta_star m q (a:w) = together $ norm[(ndelta_star m q' w) | q'<-(nap (ndelta m) q a)]

testns1 = ndelta_star endaab 1 "aaaaaaaaaa"
testns2 = ndelta_star endaab 1 "aaaaaaaaaabb"

-- this should be 'or' because we only need one subset to overlap
naccept :: Ord a => NFSM a -> [Char] -> Bool
-- there is probably a more efficent way to do this
naccept m w = or[(overlap (ndelta_star m s w) (nfinals m)) | s<-(nstarts m)]

testaccept1 = naccept ttla "aaabb"
testaccept2 = naccept ttla "aaabbbb"
testaccept3 = naccept endaab "ababab"
testaccept4 = naccept endaab "baaaab"


----------------------------------------------------------------
-- Nondeterministic FSMs with epsilon moves
data EFSM a = EFSM {
  estates :: [a],
  estarts :: [a],
  efinals :: [a],
  edelta  :: [(a,Char,a)],
  epsilon :: [(a,a)]
  }

instance Show a => Show (EFSM a) where
    show m = "("   ++ show (estates m) ++
             ", "   ++ show (estarts m) ++
             ", "  ++ show (efinals m) ++
             ", [" ++ steps(edelta m) ++ "]" ++
             ", " ++ show (epsilon m) ++ ")" where
      steps [] = []
      steps [t] = step t
      steps (t:ts) = step t ++ "," ++ steps ts
      step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'

--student example on piazza
m1 = EFSM{
 estates = [1..6],
 estarts = [1],
 efinals = [6],
 edelta  = [(2,'a',6),(4,'a',5)],
 epsilon = [(1,2),(2,3),(6,5),(5,2)]
}

--example from lecture L(m) is a*b*a*
abastar = EFSM{
 estates = [1..3],
 estarts =[1],
 efinals = [3],
 edelta = [(1,'a',1), (2,'b',2),(3,'a',3)],
 epsilon = [(1,2),(2,3)]
}

aabe = EFSM{ -- string ends with aab
 estates = [0..4],
 estarts = [0],
 efinals = [4],
 edelta = [(0,'a',0),(0,'b',0), (1,'a',2),(2,'a',3),(3,'b',4)],
 epsilon = [(0,1)]
}

abab = EFSM{ -- string contains abab
 estates = [0..6],
 estarts = [0],
 efinals = [6],
 edelta  = [(0,'a',0),(0,'b',0),(1,'a',2),(2,'b',3),(3,'a',4),(4,'b',5),(6,'a',6),(6,'b',6)],
 epsilon = [(0,1),(5,6)]
}
-- Normalized epsilon closure of a set of states
-- (Hint: look at definition of reachable below)
--copy only the qs
--reachable (FSM {states=qs, start=s, finals=fs, delta=d}) =
--  FSM {states=qs', start=s, finals=fs', delta=d'} where
--    qs' = sort $ stable $ iterate close ([s], [])
--    stable ((fr,qs):rest) = if null fr then qs else stable rest
    -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
--    close (fr, xs) = (fr', xs') where
--      xs' = fr ++ xs
--      fr' = norm $ filter (`notElem` xs') (concatMap step fr)
--      step q = map (ap d q) sigma

--change start states and step,  should only compute epsilon transitions
-- to get epsilon transitions -> epsilon m
eclose :: Ord a => EFSM a -> [a] -> [a]
eclose m qs = sort $ stable $ iterate close (qs, []) where -- change [s] to qs
              stable ((fr,qs):rest) = if null fr then qs else stable rest
              close (fr, xs) = (fr', xs') where
                xs' = fr ++ xs
                fr' = norm $ filter (`notElem` xs') (concatMap step fr)
                step q = norm [b | (a,b)<-( epsilon m ), a == q] -- step only through epsilon transitions


-- edelta_star m q w == eclosed list of states m goes to from q on w
--ndelta_star m q [] = [q]
--ndelta_star m q (a:w) = together $ norm[(ndelta_star m q' w) | q'<-(nap (ndelta m) q a)]

edh :: Ord a => EFSM a -> [a] -> Char -> [a] -- delta hat page 51
edh m [] a = []
edh m x a = together $ norm [ nap (edelta m) q a | q <- (eclose m x)] -- x must be epsilon closed

edelta_star :: Ord a => EFSM a -> [a] -> [Char] -> [a] -- def of delta hat star on page 52
edelta_star m x [] = eclose m x
edelta_star m x (a:w) = edelta_star m (edh m x a) w

-- naccept from above
--naccept m w = or[(overlap (ndelta_star m s w) (nfinals m)) | s<-(nstarts m)]
eaccept :: Ord a => EFSM a -> [Char] -> Bool
eaccept m w = or[(overlap (edelta_star m [s] w) (efinals m))| s<-(estarts m)]

----------------------------------------------------------------
-- Machine conversions

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm m = NFSM {
  nstates = states m,
  nstarts = [start m],
  nfinals = finals m,
  ndelta  = delta m
  }


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm m = FSM {
   states = subsequences (nstates m),
   start  = nstarts m,
   finals = [ x | x <-(subsequences (nstates m)), overlap x (nfinals m)],
   delta  = together $ norm[ [(x, a, together [(nap (ndelta m) q a) | q<- x]) | x <-(subsequences (nstates m))] | a <- sigma] --each state in the machine is a subset
}

-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm m =  FSM{
  states = subsequences (estates m),
  start  = eclose m (estarts m),
  finals = [ x | x <-(subsequences (estates m)), overlap x (efinals m)],
  delta  = together $ norm[ [(x, a, (eclose m (edh m x a)))| x <-(subsequences (estates m))] | a <- sigma]
}


{- Tests:

1. m and fsm_to_nfsm m accept the same strings
2. m and nfsm_to_fsm m accept the same strings
3. m and efsm_to_fsm m accept the same strings
-
-}

--using dr. wilsons test from his BFSM implementation
strings = concat $ [replicateM i "ab" | i <- [0..10]]

--1. m and fsm_to_nfsm m accept the same strings
test1a = [w | let m = (fsm_to_nfsm evena) , w<-strings, accept1 evena w /= naccept m w]
test1b = [w | let m = (fsm_to_nfsm no_aaa) , w<-strings, accept1 no_aaa w /= naccept m w]
--2. m and fsm_to_nfsm m accept the same strings
test2a = [w | let m = (nfsm_to_fsm endaab) , w<-strings, accept1 m w /= naccept endaab w]
test2b = [w | let m = (nfsm_to_fsm ttla) , w<-strings, accept1 m w /= naccept ttla w]

--3. m and efsm_to_fsm m accept the same strings
test3a = [w | let m = (efsm_to_fsm abastar) , w<-strings, accept1 m w /= eaccept abastar w]
test3b = [w | let m = (efsm_to_fsm aabe) , w<-strings, accept1 m w /= eaccept aabe w]
test3c = [w | let m = (efsm_to_fsm abab) , w<-strings, accept1 m w /= eaccept abab w]
test3d = [w | let m = (efsm_to_fsm m1) , w<-strings, accept1 m w /= eaccept m1 w]
---- Lab 8 ends here ----------------------------------------------------

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable (FSM {states=qs, start=s, finals=fs, delta=d}) =
  FSM {states=qs', start=s, finals=fs', delta=d'} where
    qs' = sort $ stable $ iterate close ([s], [])
    fs' = filter (`elem` qs') fs
    d'  = filter (\(q,_,_) -> q `elem` qs') d
    stable ((fr,qs):rest) = if null fr then qs else stable rest
    -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
    close (fr, xs) = (fr', xs') where
      xs' = fr ++ xs
      fr' = norm $ filter (`notElem` xs') (concatMap step fr)
      step q = map (ap d q) sigma


-- Change the states of an FSM from an equality type to Int
intify :: Eq a => FSM a -> FSM Int
intify m = FSM {
  states = map index (states m),
  start  = index (start m),
  finals = map index (finals m),
  delta  = [(index q, a, index q') | (q,a,q') <- delta m]
  } where
    index q = lookup (states m) q
    lookup (q':qs) q = if q == q' then 0 else 1 + lookup qs q
