module Main where

import System.IO
import Control.Monad

import Expr (fullSimplify)
import PrintExpr (printExpr)
import ParseExpr (parseExpr)

read' :: IO String
read' = putStr "> " >> hFlush stdout >> getLine

main :: IO ()
main = forever $ do
  input <- read'
  putStrLn $ printExpr $ fullSimplify $ parseExpr $ input
