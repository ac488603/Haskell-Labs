import Data.List (nub)

--Adam Castillo
--108485851

---- String operations (note: String = [Char])

-- Length and concatenation (Def 2.2, reimplements len and ++)
strlen :: String -> Int
strlen "" = 0
strlen xs = 1 + strlen (tail xs)

strcat :: String -> String -> String
strcat "" xs = xs
strcat xs ys = (head xs) : strcat (tail xs) ys


---- Language operations. Assume inputs contain no duplicates, and insure that
---- outputs also contain no duplicates

type Language = [String]

lang1 :: Language
lang1 = ["a","b","e"]

lang2 :: Language
lang2 = ["a","b","l","k"]

-- Union of languages
union_lang :: Language -> Language -> Language
union_lang [] l2 = l2
union_lang l1 l2 = nub((head l1) : union_lang (tail l1) l2)

-- Concatenation of languages (Def 2.5)
concat_lang :: Language -> Language -> Language
concat_lang [] l2 = []
concat_lang l1 l2 = nub[strcat a b |a <-l1, b<-l2]

-- L^n = L * L * ... * L (n times)
power_lang :: Language -> Int -> Language
power_lang l n 
    |n == 0    = []
    |n == 1    = l
    |otherwise  = concat_lang (power_lang l (n-1)) l

-- Bounded Kleene star, L* = L^0 U L^1 U L^2 U ... U L^n
bstar_lang :: Language -> Int -> Language
bstar_lang l n
    | n == 0 = []
    | n == 1 = l
    |otherwise  = union_lang (power_lang l n) (bstar_lang  l (n-1))

-- Reimplements elem for Languages
element :: String -> Language -> Bool
element xs [] = False
element xs l
    |((head l) == xs)   = True
    |otherwise          = element xs (tail l)

-- L1 subset L2
subset :: Language -> Language -> Bool
subset [] l2 = True
subset l1 l2 
    |(element (head l1) l2) == False = False
    |otherwise                       = subset (tail l1) l2
---- Regular expressions and the languages they denote 
---- type RegExp has 5 constructors
---- str takes 1 argument 
---- cat takes two arguments 
---- union takes 2 arguments 
---- star takes 1 argument 

data RegExp = Empty
             | Str String
             | Cat RegExp RegExp
             | Union RegExp RegExp
             | Star RegExp

-- [[r]], except use bound 5 for Kleene star
-- 
lang_of :: RegExp -> Language
lang_of (Empty)      = []
lang_of (Str a)      = [a]
lang_of (Cat r1 r2)  = concat_lang (lang_of r1) (lang_of r2)
lang_of (Union r1 r2)= union_lang  (lang_of r1) (lang_of r2)
lang_of (Star r)     = bstar_lang (lang_of r)  5       
