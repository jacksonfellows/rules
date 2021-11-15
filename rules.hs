{-# OPTIONS_GHC -Wall #-}

import Data.Char
import Control.Monad
import Control.Applicative
import Data.List
import Control.Arrow
import GHC.Real (Ratio ((:%)))

-- parsing helpers (copied from http://dev.stephendiehl.com/fun/002_parsers.html)

newtype Parser a = Parser { parse :: String -> [(a,String)] }

runParser :: Parser a -> String -> a
runParser m s =
  case parse m s of
    [(res, [])] -> res
    [(_, _)]   -> error "Parser did not consume entire stream."
    _           -> error "Parser error."

item :: Parser Char
item = Parser $ \s ->
  case s of
   []     -> []
   (c:cs) -> [(c,cs)]

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p f = Parser $ \s -> concatMap (\(a, s') -> parse (f a) s') $ parse p s

unit :: a -> Parser a
unit a = Parser (\s -> [(a,s)])

instance Functor Parser where
  fmap f (Parser cs) = Parser (\s -> [(f a, b) | (a, b) <- cs s])

instance Applicative Parser where
  pure = return
  (Parser cs1) <*> (Parser cs2) = Parser (\s -> [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1])

instance Monad Parser where
  return = unit
  (>>=)  = bind

instance MonadPlus Parser where
  mzero = failure
  mplus = combine

instance Alternative Parser where
  empty = mzero
  (<|>) = option

combine :: Parser a -> Parser a -> Parser a
combine p q = Parser (\s -> parse p s ++ parse q s)

failure :: Parser a
failure = Parser (\_ -> [])

option :: Parser a -> Parser a -> Parser a
option  p q = Parser $ \s ->
  case parse p s of
    []     -> parse q s
    res    -> res

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = item `bind` \c ->
  if p c
  then unit c
  else (Parser (\_ -> []))

oneOf :: [Char] -> Parser Char
oneOf s = satisfy (flip elem s)

notOneOf :: [Char] -> Parser Char
notOneOf s = satisfy (not . flip elem s)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) <|> return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do {a <- p; rest a}
  where rest a = (do f <- op
                     b <- p
                     rest (f a b))
                 <|> return a

char :: Char -> Parser Char
char c = satisfy (c ==)

natural :: Parser Integer
natural = read <$> some (satisfy isDigit)

string :: String -> Parser String
string [] = return []
string (c:cs) = do { _ <- char c; _ <- string cs; return (c:cs)}

token :: Parser a -> Parser a
token p = do { a <- p; _ <- spaces ; return a}

reserved :: String -> Parser String
reserved s = token (string s)

spaces :: Parser String
spaces = many $ oneOf " \n\r"

digit :: Parser Char
digit = satisfy isDigit

number :: Parser Integer
number = do
  s <- string "-" <|> return []
  cs <- some digit
  return $ read (s ++ cs)

parens :: Parser a -> Parser a
parens m = do
  _ <- reserved "("
  n <- m
  _ <- reserved ")"
  return n

-- end parsing helpers

data Expr = Num Rational
          | Var String
          | Sum [(Expr,Rational)]
          | Product [(Expr,Rational)]
          | Expt Expr Expr
          deriving (Show,Eq,Ord)

isNum :: Expr -> Bool
isNum (Num _) = True
isNum _ = False

isSum :: Expr -> Bool
isSum (Sum _) = True
isSum _ = False

isProduct :: Expr -> Bool
isProduct (Product _) = True
isProduct _ = False

isExpt :: Expr -> Bool
isExpt (Expt _ _) = True
isExpt _ = False

sortExpr :: Expr -> Expr
sortExpr (Sum xs) = Sum $ sort $ map (first sortExpr) xs
sortExpr (Product xs) = Product $ sort $ map (first sortExpr) xs
sortExpr (Expt a b) = Expt (sortExpr a) (sortExpr b)
sortExpr e = e

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy (\a b -> f a == f b)

addCoefsAdjLikeTerms :: Eq a => [(a,Rational)] -> [(a,Rational)]
addCoefsAdjLikeTerms xs = map (\xs'@((a,_):_) -> (a,sum $ map snd xs')) $ groupOn fst xs

collectLikeTerms :: Expr -> Expr
collectLikeTerms (Sum xs) = Sum $ addCoefsAdjLikeTerms $ map (first collectLikeTerms) xs
collectLikeTerms (Product xs) = Product $ addCoefsAdjLikeTerms $ map (first collectLikeTerms) xs
collectLikeTerms (Expt a b) = Expt (collectLikeTerms a) (collectLikeTerms b)
collectLikeTerms e = e

foldConstantTerm :: (Rational -> Rational -> Rational) -> (Expr,Rational) -> (Expr,Rational)
foldConstantTerm f (Num n,i) = (Num $ f n i,1)
foldConstantTerm _ t = t

groupConstants :: (Rational -> Rational -> Rational) -> [(Expr,Rational)] -> [(Expr,Rational)]
groupConstants f xs = concatMap (simp f) $ groupOn snd $ sortOn snd xs

simp :: (Rational -> Rational -> Rational) -> [(Expr,Rational)] -> [(Expr,Rational)]
simp f e@((_,1):_)
  | null cnst = rest
  | otherwise = (Num $ foldl1 f $ map (\(Num x) -> x) $ map fst cnst,1) : rest
  where (cnst,rest) = partition (isNum . fst) e
simp _ e = e

wrapUnlessConst :: ([(Expr,Rational)] -> Expr) -> [(Expr,Rational)] -> Expr
wrapUnlessConst _ [(x@(Num _),1)] = x
wrapUnlessConst f xs = f xs

ratPow :: Rational -> Rational -> Rational
ratPow a (b:%1) = a ^^ b
ratPow a b = error $ "cannot raise " ++ show a ++ " to " ++ show b

foldConstants :: Expr -> Expr
foldConstants (Sum xs) = wrapUnlessConst Sum $ groupConstants (+) $ map (foldConstantTerm (*)) $ map (first foldConstants) xs
foldConstants (Product xs) = wrapUnlessConst Product $ groupConstants (*) $ map (foldConstantTerm ratPow) $ map (first foldConstants) xs
foldConstants (Expt a b) = case a' of
  Num a'' -> case b' of
    Num b'' -> Num $ ratPow a'' b''
    _ -> Expt a' b'
  _ -> Expt a' b'
  where a' = foldConstants a
        b' = foldConstants b
foldConstants e = e

stripIdentities :: Expr -> Expr
stripIdentities (Sum []) = Num 0
stripIdentities (Sum [(x,1)]) = stripIdentities x
stripIdentities (Product []) = Num 1
stripIdentities (Product [(x,1)]) = stripIdentities x
stripIdentities (Sum xs) = Sum $ filter ((/= (Num 0)) . fst) $ filter ((/= 0) . snd) $ map (first stripIdentities) xs
stripIdentities (Product xs) = Product $ filter ((/= (Num 1)) . fst) $ filter ((/= 0) . snd) $ map (first stripIdentities) xs
stripIdentities (Expt a b)
  | a' == Num 0 = Num 0
  | a' == Num 1 = Num 1
  | b' == Num 0 = Num 1
  | b' == Num 1 = a'
  | otherwise = Expt a' b'
  where a' = stripIdentities a
        b' = stripIdentities b
stripIdentities e = e

flatten :: Expr -> Expr
flatten (Sum xs) = Sum $ (concatMap (\((Sum xs'),c) -> map (\(x,c') -> (x,c*c')) xs') sums) ++ rest
  where (sums,rest) = partition (isSum . fst) $ map (first flatten) xs
flatten (Product xs) = Product $ (concatMap (\((Product xs'),c) -> map (\(x,c') -> (x,c*c')) xs') products) ++ rest
  where (products,rest) = partition (isProduct . fst) $ map (first flatten) xs
flatten (Expt a b) = Expt (flatten a) (flatten b)
flatten e = e

flattenProduct :: (Expr,Rational) -> (Expr,Rational)
flattenProduct (Product [(Num n,1),(x,1)],c) = (x,n*c)
flattenProduct (Product ((Num n,1):xs),c) = (Product xs,n*c)
flattenProduct e' = e'

flattenProductsInSums :: Expr -> Expr
flattenProductsInSums (Sum xs) = Sum $ map flattenProduct $ map (first flattenProductsInSums) xs
flattenProductsInSums (Product xs) = Sum $ [flattenProduct (Product $ map (first flattenProductsInSums) xs,1)]
flattenProductsInSums (Expt a b) = Expt (flattenProductsInSums a) (flattenProductsInSums b)
flattenProductsInSums e = e

expandSum :: (Expr,Rational) -> (Expr,Rational)
expandSum (Sum [(x,c)],1) = (Product [(Num c,1),(x,1)],1)
expandSum e = e

flattenSumsInProducts :: Expr -> Expr
flattenSumsInProducts (Product xs) = Product $ map expandSum $ map (first flattenSumsInProducts) xs
flattenSumsInProducts (Sum xs) = Sum $ map (first flattenSumsInProducts) xs
flattenSumsInProducts (Expt a b) = Expt (flattenSumsInProducts a) (flattenSumsInProducts b)
flattenSumsInProducts e = e

flattenExpts :: Expr -> Expr
flattenExpts (Sum xs) = Sum $ map (first flattenExpts) xs
flattenExpts (Product xs) = Product $ map (first flattenExpts) xs
flattenExpts (Expt a b) = case b' of
  Num b'' -> Product [(a',b'')]
  _ -> Expt a' b'
  where a' = flattenExpts a
        b' = flattenExpts b
flattenExpts e = e

simplify :: Expr -> Expr
simplify = sortExpr . stripIdentities . foldConstants . collectLikeTerms . flattenExpts . flattenSumsInProducts . flattenProductsInSums . flatten

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a = if fa == a then a else fixpoint f fa
  where fa = f a

wrapIf :: String -> Bool -> String
wrapIf s True = "(" ++ s ++ ")"
wrapIf s False = s

printRat :: Rational -> String
printRat (n:%1) = show n
printRat (n:%d) = show n ++ "/" ++ show d

printFirstSumTerm :: (Expr,Rational) -> String
printFirstSumTerm (x,1) = (printExpr x) `wrapIf` (isSum x)
printFirstSumTerm (x,-1) = "-" ++ (printExpr x) `wrapIf` (isSum x)
printFirstSumTerm (x,c) = printRat c ++ "*" ++ (printExpr x) `wrapIf` (isSum x)

printSumTerm :: (Expr,Rational) -> String
printSumTerm (x,1) = "+" ++ (printExpr x) `wrapIf` (isSum x)
printSumTerm (x,-1) = "-" ++ (printExpr x) `wrapIf` (isSum x)
printSumTerm (x,c) = "+" ++ printRat c ++ "*" ++ (printExpr x) `wrapIf` (isSum x)

printProductTerm :: (Expr,Rational) -> String
printProductTerm (x,1) = (printExpr x) `wrapIf` (isSum x || isProduct x)
printProductTerm (x,c) = (printExpr x) `wrapIf` (isSum x || isProduct x) ++ "^" ++ printRat c

printExpr :: Expr -> String
printExpr (Sum []) = ""
printExpr (Sum (x:xs)) = printFirstSumTerm x ++ concatMap printSumTerm xs
printExpr (Product xs)
  | null p && null n = ""
  | null n = intercalate "*" $ map printProductTerm p
  | null p = "1/" ++ (intercalate "*" $ map printProductTerm n') `wrapIf` (length n' > 1)
  | otherwise = intercalate "*" (map printProductTerm p) ++ "/" ++ (intercalate "*" $ map printProductTerm n') `wrapIf` (length n' > 1)
  where (p,n) = partition ((> 0) . snd) xs
        n' = map (second abs) n
printExpr (Expt a b) = (printExpr a) `wrapIf` (isSum a || isProduct a) ++ "^" ++ (printExpr b) `wrapIf` (isSum b || isProduct b || isExpt b)
printExpr (Num n) = printRat n
printExpr (Var v) = v

data Expr' = Add Expr' Expr'
           | Sub Expr' Expr'
           | Mul Expr' Expr'
           | Div Expr' Expr'
           | Expt' Expr' Expr'
           | Minus Expr'
           | Num' Rational
           | Var' String
           deriving Show

convertExpr' :: Expr' -> Expr
convertExpr' (Add a b) = Sum [(convertExpr' a,1), (convertExpr' b,1)]
convertExpr' (Sub a b) = Sum [(convertExpr' a,1), (convertExpr' b,-1)]
convertExpr' (Mul a b) = Product [(convertExpr' a,1), (convertExpr' b,1)]
convertExpr' (Div a b) = Product [(convertExpr' a,1), (convertExpr' b,-1)]
convertExpr' (Expt' a b) = Expt (convertExpr' a) (convertExpr' b)
convertExpr' (Minus a) = Sum [(convertExpr' a,-1)]
convertExpr' (Num' n) = Num n
convertExpr' (Var' v) = Var v

num' :: Parser Expr'
num' = Num' . toRational <$> number

neg :: Parser Expr' -> Parser Expr'
neg f = do
  _ <- reserved "-"
  a <- f
  return $ Minus a

var' :: Parser Expr'
var' = do
  h <- satisfy isAlpha
  r <- many (notOneOf " +-*/^()")
  return $ Var' $ h:r

atom :: Parser Expr'
atom = num' <|> var'

infixOp :: String -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = reserved x >> return f

addop :: Parser (Expr' -> Expr' -> Expr')
addop = (infixOp "+" Add) <|> (infixOp "-" Sub)

mulop :: Parser (Expr' -> Expr' -> Expr')
mulop = (infixOp "*" Mul) <|> (infixOp "/" Div)

exptop :: Parser (Expr' -> Expr' -> Expr')
exptop = infixOp "^" Expt'

factor' :: Parser Expr'
factor' = chainl1 factor exptop

factor :: Parser Expr'
factor = parens expr' <|> neg var' <|> neg (parens expr') <|> token atom

term :: Parser Expr'
term = chainl1 factor' mulop

expr' :: Parser Expr'
expr' = chainl1 term addop

parseExpr' :: String -> Expr'
parseExpr' = runParser expr'
