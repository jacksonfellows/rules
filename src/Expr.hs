module Expr
  ( Expr (..)
  , isSum
  , isProduct
  , isExpt
  , fullSimplify
  ) where

import GHC.Real (Ratio ((:%)))
import Data.List
import Control.Arrow

data Expr = Num Rational
          | Var String
          | Sum [(Expr,Rational)]
          | Product [(Expr,Rational)]
          | Expt Expr Expr
          | Rule Expr Expr
          | Replace Expr Expr
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
sortExpr (Rule a b) = Rule (sortExpr a) (sortExpr b)
sortExpr (Replace a b) = Replace (sortExpr a) (sortExpr b)
sortExpr e@(Var _) = e
sortExpr e@(Num _) = e

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy (\a b -> f a == f b)

addCoefsAdjLikeTerms :: Eq a => [(a,Rational)] -> [(a,Rational)]
addCoefsAdjLikeTerms xs = map (\xs'@((a,_):_) -> (a,sum $ map snd xs')) $ groupOn fst xs

collectLikeTerms :: Expr -> Expr
collectLikeTerms (Sum xs) = Sum $ addCoefsAdjLikeTerms $ map (first collectLikeTerms) xs
collectLikeTerms (Product xs) = Product $ addCoefsAdjLikeTerms $ map (first collectLikeTerms) xs
collectLikeTerms (Expt a b) = Expt (collectLikeTerms a) (collectLikeTerms b)
collectLikeTerms (Rule a b) = Rule (collectLikeTerms a) (collectLikeTerms b)
collectLikeTerms (Replace a b) = Replace (collectLikeTerms a) (collectLikeTerms b)
collectLikeTerms e@(Var _) = e
collectLikeTerms e@(Num _) = e

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
foldConstants (Rule a b) = Rule (foldConstants a) (foldConstants b)
foldConstants (Replace a b) = Replace (foldConstants a) (foldConstants b)
foldConstants e@(Var _) = e
foldConstants e@(Num _) = e

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
stripIdentities (Rule a b) = Rule (stripIdentities a) (stripIdentities b)
stripIdentities (Replace a b) = Replace (stripIdentities a) (stripIdentities b)
stripIdentities e@(Var _) = e
stripIdentities e@(Num _) = e

flatten :: Expr -> Expr
flatten (Sum xs) = Sum $ (concatMap (\((Sum xs'),c) -> map (\(x,c') -> (x,c*c')) xs') sums) ++ rest
  where (sums,rest) = partition (isSum . fst) $ map (first flatten) xs
flatten (Product xs) = Product $ (concatMap (\((Product xs'),c) -> map (\(x,c') -> (x,c*c')) xs') products) ++ rest
  where (products,rest) = partition (isProduct . fst) $ map (first flatten) xs
flatten (Expt a b) = Expt (flatten a) (flatten b)
flatten (Rule a b) = Rule (flatten a) (flatten b)
flatten (Replace a b) = Replace (flatten a) (flatten b)
flatten e@(Var _) = e
flatten e@(Num _) = e

flattenProduct :: (Expr,Rational) -> (Expr,Rational)
flattenProduct (Product [(Num n,1),(x,1)],c) = (x,n*c)
flattenProduct (Product ((Num n,1):xs),c) = (Product xs,n*c)
flattenProduct e = e

flattenProductsInSums :: Expr -> Expr
flattenProductsInSums (Sum xs) = Sum $ map flattenProduct $ map (first flattenProductsInSums) xs
flattenProductsInSums (Product xs) = Sum $ [flattenProduct (Product $ map (first flattenProductsInSums) xs,1)]
flattenProductsInSums (Expt a b) = Expt (flattenProductsInSums a) (flattenProductsInSums b)
flattenProductsInSums (Rule a b) = Rule (flattenProductsInSums a) (flattenProductsInSums b)
flattenProductsInSums (Replace a b) = Replace (flattenProductsInSums a) (flattenProductsInSums b)
flattenProductsInSums e@(Var _) = e
flattenProductsInSums e@(Num _) = e

expandSum :: (Expr,Rational) -> (Expr,Rational)
expandSum (Sum [(x,c)],1) = (Product [(Num c,1),(x,1)],1)
expandSum e = e

flattenSumsInProducts :: Expr -> Expr
flattenSumsInProducts (Product xs) = Product $ map expandSum $ map (first flattenSumsInProducts) xs
flattenSumsInProducts (Sum xs) = Sum $ map (first flattenSumsInProducts) xs
flattenSumsInProducts (Expt a b) = Expt (flattenSumsInProducts a) (flattenSumsInProducts b)
flattenSumsInProducts (Rule a b) = Rule (flattenSumsInProducts a) (flattenSumsInProducts b)
flattenSumsInProducts (Replace a b) = Replace (flattenSumsInProducts a) (flattenSumsInProducts b)
flattenSumsInProducts e@(Var _) = e
flattenSumsInProducts e@(Num _) = e

flattenExpts :: Expr -> Expr
flattenExpts (Sum xs) = Sum $ map (first flattenExpts) xs
flattenExpts (Product xs) = Product $ map (first flattenExpts) xs
flattenExpts (Expt a b) = case b' of
  Num b'' -> Product [(a',b'')]
  _ -> Expt a' b'
  where a' = flattenExpts a
        b' = flattenExpts b
flattenExpts (Rule a b) = Rule (flattenExpts a) (flattenExpts b)
flattenExpts (Replace a b) = Replace (flattenExpts a) (flattenExpts b)
flattenExpts e@(Var _) = e
flattenExpts e@(Num _) = e

simplify :: Expr -> Expr
simplify = sortExpr . stripIdentities . foldConstants . collectLikeTerms . flattenExpts . flattenSumsInProducts . flattenProductsInSums . flatten

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a = if fa == a then a else fixpoint f fa
  where fa = f a

fullSimplify :: Expr -> Expr
fullSimplify = fixpoint simplify
