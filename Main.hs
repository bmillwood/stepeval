module Main (main, getLines) where

import Control.Applicative
import Control.Monad
import Language.Haskell.Exts
import LambdaCaseLet
import System.IO

main :: IO ()
main = do
 putStrLn "Enter a string to parse, terminated by a blank line:"
 exp <- unlines <$> getLines
 case parseExp exp of
  ParseOk e -> forM_ (itereval e) $
   (>> (hFlush stdout >> getLine)) . putStr . prettyPrint
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."

getLines :: IO [String]
getLines = do
 line <- getLine
 if null line then return [] else (line :) <$> getLines
