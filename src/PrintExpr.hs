module PrintExpr
  ( printExpr
  ) where

import GHC.Real (Ratio ((:%)))
import Data.List
import Control.Arrow

import Expr

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
printExpr (Rule a b) = printExpr a ++ "->" ++ printExpr b
