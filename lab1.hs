---- CSci 119, Lab 1 ----

--ADAM CASTILLO
--108485851

-- Note: you will replace all instances of "undefined" below with your answers.

---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and  [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc = and[ ( a && (b && c)) == ((a && b) && c) | a <-bools,  b <-bools, c <-bools]
or_assoc =  and[ ( a || (b || c)) == ((a || b) || c) | a <-bools,  b <-bools, c <-bools]
and_dist = and[(a && (b || c)) == ((a && b) || ( a&&c )) | a <-bools,  b <-bools, c <-bools]
or_dist = and[(a || (b && c)) == ((a || b) && ( a || c )) | a <-bools,  b <-bools, c <-bools]
          
-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(a /= b) == (b /= a) | a <- bools, b <- bools]
xor_assoc    = and [ (a /= (b /= c)) == (( a /= b) /= c)|a <-bools, b <-bools, c <-bools]
xor_dist_and = and [(a /= (b && c)) == ((a /= b) && (a /= c)) |a <-bools, b <-bools, c <-bools] 
xor_dist_or  = and [(a /= (b || c)) == ((a /= b) || (a /= c)) |a <-bools, b <-bools, c <-bools]
and_dist_xor = and [(a && (b /= c)) == ((a && b) /= (a && c)) |a <-bools, b <-bools, c <-bools]
or_dist_xor  = and [(a || (b /= c)) == ((a || b) /= (a || c)) |a <-bools, b <-bools, c <-bools]
               
-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [(a <= (b <= c)) == ((a <= b) <= c) |a <-bools, b <-bools, c <-bools]
comm_imp = and[(a <= b) == (b <= a) |a <-bools, b <-bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.

u = [1..8]
u1= [1,5,6,7,15,34]
-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.

-- 1. "Every number that's greater than 2 is greater than 1"
-- A: forall n, (n > 2) imp (n > 1)
prob1 = and [(n > 2) <= (n > 1) | n <- u]

-- 2. Every number is either greater than 1 or less than 2
-- A: for all a, a >1 or a < 2
prob2 = and[(a > 1) || (a < 2)| a <-u]

-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: forall a, forall b,  a<=b or b <=a 
prob3 = and[(a<=b) || (b<=a)|a <-u, b <-u]

-- 4. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A: forall odd a ,  exists even b,  b > a 
prob4 = and[or[ b > a| b <-u, even b]|a <-u, odd a]

-- 5. For every even number, there is a greater odd number
-- A: forall odd a ,  exists even b,  a > b 
prob5 = and[or[ b > a| b <-u, odd b]|a <-u, even a]

-- 6. There are two odd numbers that add up to 6
-- A: exsits odd a, exists odd b,  a+b == 6
prob6 = or[a+b ==6 |a <-u, b <-u,  odd a, odd b]

-- 7. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- A: exists a,  forall b,  a >=b
prob7 = and[or[a >= b| b <-u ]| a <-u]

-- 8. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: forall a,  exists b, exists c, (a < b) imp (c < a) or (c > b)
prob8 = and[or[((a < b) <= (c < a) || (c > b))| a <-u1, c <-u1, b <-u1, a/=b, a/=c, b /=c ]]
