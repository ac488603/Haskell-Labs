-- CSci 119, Lab 5
--Adam Castillo 
--108485851

-- Reference: Lecture notes, Sections 4.1, 4.2

sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

--a machine that accepts atleast 1 b 
exb :: FSM
exb = ([0,1], 0, [1],[(0,'a',0),(0,'b',1), (1,'a',1),(1,'b',1)]) 

exa :: FSM
exa = ([0,1],0,[1],[(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 1)])

twoa :: FSM
twoa = ([0,1,2],0,[2],[(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2,'a',2),(2,'b',2)])

oddb :: FSM
oddb = ([0,1],0,[1],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])

noaab :: FSM
noaab = ([0,1,2,3],0,[0,1,2],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),(2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3),(0,' ',0)])


-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)
noDup :: Eq a => [a] -> Bool
noDup [] = True
noDup (q:qs) = if (elem q qs) then False else (noDup qs)

exist :: Eq a => a -> [a] -> Bool
exist p [] = False
exist p qs = elem p qs 

subset :: Eq a => [a] -> [a] -> Bool
subset [] qs = True 
subset (f:fs) qs 
    | not (elem f qs) = False
    |otherwise  = subset fs qs

cart :: [a] -> [b] ->[(a,b)]
cart [] ys = []
cart xs ys = [(x,y)| x <-xs, y <-ys] 

-- take first to elements of a tuple
first2 :: [(a,b,c)]->[(a,b)]
first2 [] = []  
first2 ((a,b,c):xs) = (a,b) : first2 xs

regroup :: (a,b,c)->((a,b),c)
regroup (a,b,c) = ((a,b),c) 
 
checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = ((noDup qs) && (exist q0 qs) && (subset fs qs) && ((noDup(first2 ts)) && (subset(cart qs sigma) (first2 ts))))  


-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q

-- returns the resulting state given a current state and a character 
delta :: FSM -> Int -> Char -> Int
delta (qs, q0, fs, (t:ts)) q a 
    | fst (regroup t) == (q,a) = snd (regroup t)
    | otherwise = delta (qs,q0,fs,ts) q a

-- Gives the delta* function
-- returns a state after processing a string of characters
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q [] = q
delta_star m q (w:ws) = delta_star m (delta m q w) ws

-- Machine acceptance, Definition 1 (via delta*)
--check if delta_star result is in final states
accept1 :: FSM -> [Char] -> Bool
accept1 (qs, q0, fs, ts) w = exist (delta_star (qs, q0, fs, ts) q0 w) fs 


-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux (qs, q0, fs, ts) q [] = exist q fs
accept2_aux m q (w:ws) = (accept2_aux m (delta m q w) ws)

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 (qs, q0, fs, ts) w = accept2_aux (qs, q0, fs, ts) q0 w  


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately

-- accepts empty string 
evena :: FSM
evena = ([0,1],0,[0],[(0,'a',1),(0,'b',0),(1,'a',0),(1,'b',1),(0,' ',0)])

testa1 = accept1 evena "abababababa"
testa2 = accept2 evena "abababababa"
testa3 = accept1 evena "ababababaaaaaaa"
testa4 = accept2 evena "ababababaaaaaaa"

-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately

-- accepts empty string 
noaaa :: FSM
noaaa = ([0,1,2,3],0,[0,1,2],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),(2,'a',3),(2,'b',0),(3,'a',3),(3,'b',3),(0,' ',0)])

testnoa1 = accept1 noaaa "abababababa"
testnoa2 = accept2 noaaa "abababababa"
testnoa3 = accept1 noaaa "abababababaababaaab"
testnoa4 = accept2 noaaa "abababababaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab"
