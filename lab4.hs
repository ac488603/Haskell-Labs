-- CSci 119, Lab 4
--Adam Castillo
--108485851
---- Regular expressions, along with input and output
data RegExp = Empty
             | Letter Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


---------------- Part 1 ----------------

-- Implement the six recursive predications/operations on RegExp given in
-- Section 3.3 of the notes. Each should begin with a type declaration.
-- Include several tests for each function.

-- The language is empty 
emptiness :: RegExp -> Bool 
emptiness Empty = True
emptiness (Letter a) = False
emptiness (Union r1 r2) = (emptiness r1) && (emptiness r2) 
emptiness (Cat r1 r2) = (emptiness r1) || (emptiness r2)
emptiness (Star r) = False 

teste1 = emptiness(toRE"@")
teste2 = emptiness(toRE"a")
teste3 = emptiness(toRE"@@+")
teste4 = emptiness(toRE"a@.")
teste5 = emptiness(toRE"@*")

--set that is epsilon
unitarity :: RegExp -> Bool
unitarity Empty = False
unitarity (Letter a) = False
unitarity (Union r1 r2) = (((unitarity r1) && (emptiness r2)) || ((emptiness r1) && (unitarity r2)) || ((unitarity r1) && (unitarity r2)))
unitarity (Cat r1 r2) = (unitarity r1) && (unitarity r2) 
unitarity (Star r) = (emptiness r) || (unitarity r)

testu1 = unitarity(toRE"@")
testu2 = unitarity(toRE"a")
testu3= unitarity(toRE"@*b+")
testu4 = unitarity(toRE"a*b*.")
testu5 = unitarity(toRE"@*")

--The language is {epsilon}
bypass :: RegExp -> Bool
bypass Empty = False
bypass (Letter a) = False
bypass (Union r1 r2) = (bypass r1) || (bypass r2)
bypass (Cat r1 r2) = (bypass r1) && (bypass r2)
bypass (Star r) = True

testb1 = bypass(toRE"@")
testb2 = bypass(toRE"a")
testb3 = bypass(toRE"a*b+")
testb4 = bypass(toRE"a*b*.")
testb5 = bypass(toRE"a*")

--the language is infinite
infinit :: RegExp -> Bool
infinit Empty = False
infinit (Letter a) = False
infinit (Union r1 r2) = (infinit r1) || (infinit r2)
infinit (Cat r1 r2)  =  (((infinit r1) && (not(emptiness r2))) ||((infinit r2) && (not(emptiness r1))))
infinit (Star r) = (not(emptiness r)) && (not(unitarity r))

testi1 = infinit(toRE"@")
testi2 = infinit(toRE"a")
testi3 = infinit(toRE"a*b+")
testi4 = infinit(toRE"ab*.")
testi5 = infinit(toRE"ab*.")

--reversves each string in a language to get a new language
rev :: RegExp -> RegExp
rev Empty = Empty
rev (Letter a) = (Letter a) 
rev (Union r1 r2) = (Union (rev r1) (rev r2))
rev (Cat r1 r2) = (Cat (rev r2) (rev r1))
rev (Star r) = (Star (rev r))

testr1 = rev(toRE"@")
testr2 = rev(toRE"a")
testr3 = rev(toRE"ab+")
testr4 = rev(toRE"abcd...")
testr5 = rev(toRE"a*b*.")
 
-- finds strings that begin with char then removes char and returns rest of string
leftq :: RegExp -> Char -> RegExp
leftq Empty s = Empty
leftq (Letter a) s = if s == a then (Star Empty) else Empty
leftq (Union r1 r2) s = (Union (leftq r1 s) (leftq r2 s))
leftq (Cat r1 r2) s = if (bypass r1) then (Union(Cat (leftq r1 s)(r2))(leftq r2 s)) else (Cat(leftq r1 s)(r2))
leftq (Star r) s = (Cat (leftq r s) (Star r)) 

testl1 = leftq(toRE"@") 'a'
testl2 = leftq(toRE"a") 'a'
testl3 = leftq(toRE"a*b+") 'a'
testl4 = leftq(toRE"ab*.") 'a'
testl5 = leftq(toRE"a*") 'a'

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits [] = []
splits xs = [(take a xs, drop a xs)| a<-[0..length(xs)]] 

tests1 = splits "abc"
tests2 = splits "erts"
tests3 = splits "adfghje"

match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Letter a) w = (a:[]) == w
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or[(match1 r1 u) && (match1 r2 v)|(u,v)<-splits w]
match1 (Star r) w = if(w == "")then True else or[(match1 r u) && (match1 (Star r) v)|(u,v)<-splits w, u /=""] 

testma1 = match1 ab "aabbaabb"
testma2 = match1 ttla "aaaababa"
testma3 = match1 ena "bbbbbababababbbb"
testma4 = match1 bb1 "baababbaabab"

--c is the mode,  0  for unrestriced,1 meaning that r1 cant match an empty string 
match2 :: [RegExp] -> String -> Bool -> Bool
match2 [] w c = w == ""
match2 ((Empty):rs) w c = False
match2 ((Letter a):rs) w c = (head w) == a && (match2 rs (tail w) False)
match2 ((Union r1 r2):rs) w c = (match2 (r1:rs) w c) || (match2 (r2:rs) w c)
match2 ((Cat r1 r2):rs) w c =  (match2  (r1:r2:rs) w c) || ((c== True) && (bypass(r1)) && (match2 (r2:rs) w True)) 
match2 ((Star r):rs) w c  = ((c == False) && (match2 rs w (c)) || (match2 (r:(Star r):rs) w (True)))

testmb1 = match2 [ab] "aabbaabb" False
testmb2 = match2 [ttla] "aaaababa" False
testmb3 = match2 [ena] "bbbbbababababbbb" False
testmb4 = match2 [bb1] "baababbaabab" False

-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once
