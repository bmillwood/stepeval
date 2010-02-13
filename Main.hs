module Main (cgiMain, cliMain, main) where

import Control.Applicative
import Control.Monad
import Data.Char
import Language.Haskell.Exts
import LambdaCaseLet
import Numeric
import System.Environment
import System.IO

main = cliMain

cliMain :: IO ()
cliMain = do
 putStrLn "Enter a string to parse, terminated by a blank line:"
 exp <- unlines <$> getLines
 case parseExp exp of
  ParseOk e -> forM_ (itereval e) $
   (>> (hFlush stdout >> getLine)) . putStr . prettyPrint
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."

cgiMain :: IO ()
cgiMain = do
 putStr "Content-Type: text/plain; charset=UTF-8\n\n"
 exp <- unescape . tail . dropWhile (/= '=') <$> getEnv "QUERY_STRING"
 case parseExp exp of
  ParseOk e -> printeval e
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."
 where unescape ('+':cs) = ' ':unescape cs
       unescape ('%':a:b:cs) = case readHex [a, b] of
        [(x, "")] -> chr x : unescape cs
        _ -> error $ "Failed to parse percent escape: " ++ [a, b]
       unescape (c:cs) = c:unescape cs
       unescape [] = ""

getLines :: IO [String]
getLines = do
 line <- getLine `catch` (const $ return "")
 if null line then return [] else (line :) <$> getLines

