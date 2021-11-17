module ParseExpr
  ( parseExpr
  ) where

import Data.Char
import Control.Applicative

import Expr
import Parser

data Expr' = Add Expr' Expr'
           | Sub Expr' Expr'
           | Mul Expr' Expr'
           | Div Expr' Expr'
           | Expt' Expr' Expr'
           | Minus Expr'
           | Num' Rational
           | Var' String
           | Rule' Expr' Expr'
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
convertExpr' (Rule' a b) = Rule (convertExpr' a) (convertExpr' b)

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

rule :: Parser Expr'
rule = do
  a <- expr'
  _ <- reserved "->"
  b <- expr'
  return $ Rule' a b

expr'' :: Parser Expr'
expr'' = rule <|> expr'

parseExpr' :: String -> Expr'
parseExpr' = runParser expr''

parseExpr :: String -> Expr
parseExpr = convertExpr' . parseExpr'
