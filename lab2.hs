---- CSci 119, Fall 2017, Lab 2 ----
--Adam Castillo 
--108485851
-- As in Lab 1, we will be working with the finite universe [1..8]
import Data.List  
u = [1..8]

----- PART 1:  Relations on u -----

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]
        
full :: Reln
full = [(a,b)| a <-u, b <-u]
-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | j <- [1..8], i <- [1..j-1]]

leq_reln :: Reln
leq_reln  = [(i,j) | j <- [1..8], i <- [1..j]]
            
-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- [1..8], j <- [1..8], (j - i) `mod` 3 == 0]

eqmod2_reln :: Reln
eqmod2_reln = [(i,j) | i <- [1..8], j <- [1..8], (j - i) `mod` 2 == 0]
-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
refl :: Reln -> Bool
refl rs = and[elem (a,a) rs| a <-u] -- check to see if relation is reflexive on universe

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
symm :: Reln -> Bool
symm rs = and[elem (a,b) rs| (b,a) <-rs]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, (a,b) in R /\ (b,c) in R -> (a,c) in R
trans :: Reln -> Bool
trans rs = and[ elem (a,c) rs|(a,b) <-rs, (b',c) <- rs, b == b']


-- Use the functions above to check the <, <=, and eqmod3 relations for
-- relexivity, symmetry, and transitivity

--leq_reln    = reflexive, transitive
--less_reln   = transitive
--eqmod3_reln = reflexive,symmetric, transitive


-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8),(1,2),(2,3),(2,1),(3,2)]
rst'_test = refl rst'&& symm rst' && not(trans rst')

-- refl, not symm, trans
rs't :: Reln
rs't = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8),(1,2)]
rs't_test = refl rs't && not(symm rs't) && trans rs't

-- refl, not symm, not trans
rs't' :: Reln
rs't' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8),(1,2),(2,3)]
rs't'_test = refl rs't' && not( symm rs't') && not (trans rs't')

-- not refl, symm, trans
r'st :: Reln
r'st = []
r'st_test = not (refl r'st) && symm r'st && trans r'st

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(1,2),(2,3),(3,2),(2,1)]
r'st'_test = not (refl r'st') && symm r'st' && not (trans r'st')

-- not refl, not symm, trans
r's't :: Reln
r's't = [(1,1),(1,2)]
r's't_test = not(refl r's't) && not(symm r's't) && trans r's't

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(1,2),(2,3)] --  provide counter example for transistive
r's't'_test = not(refl r's't') && not(symm r's't') && not(trans r's't')


---- PART 2: Partitions of u -----

-- A partitition, P, of u is a list of blocks, which are lists of elements
-- of u, that satisfies certain conditions (nontrivial, total, disjoint)

-- For example, here is the partitition of u corresponding to equivalence mod 3:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]

nontrivial:: [[Int]] -> Bool
nontrivial [] = False
nontrivial bs = and[not(null a)|a<-bs]

disjoint:: [[Int]] -> Bool
disjoint bs = and[and[not(elem b ae)| ae <-bs, b <- be, ae /= be]| be <-bs]

total:: [[Int]] -> Bool
total bs = and[or[elem a be|be<-bs]|a<-u]
-- Write a function part that tests whether a list of lists is a partition of u
part :: [[Int]] -> Bool
part bs = (nontrivial bs) && (disjoint bs) && (total bs)


-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u.

--nub removes duplicates from a list 
eq2part :: Reln -> [[Int]]
eq2part rs = nub[[ b |(a,b)<-rs, c == a]| c <-u] 

-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = [(a,b)| abs<- bs,  a<-abs, b<-abs]

--eq2part && part2eq test
test1 = eq2part(part2eq eqmod3_part) == eqmod3_part
test2 = sort(part2eq(eq2part eqmod3_reln)) == sort(eqmod3_reln)