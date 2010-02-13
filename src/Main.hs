module Main (cgiMain, cliMain, main) where

import Control.Applicative
import Control.Concurrent
import Control.Exception
import Control.Monad
import Data.Char
import Language.Haskell.Exts
import LambdaCaseLet
import Numeric
import Prelude hiding (catch)
import System.Environment
import System.IO

main :: IO ()
main = do
 e <- lookup "QUERY_STRING" <$> getEnvironment
 case e of
  Nothing -> cliMain
  Just s -> cgiMain s

cliMain :: IO ()
cliMain = do
 putStrLn "Enter a string to parse, terminated by a blank line:"
 exp <- unlines <$> getLines
 case parseExp exp of
  ParseOk e -> forM_ (itereval e) $
   (>> (hFlush stdout >> getLine)) . putStr . prettyPrint
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."
 where getLines :: IO [String]
       getLines = do
        line <- getLine
        if null line then return [] else (line :) <$> getLines

cgiMain :: String -> IO ()
cgiMain qstr = do
 putStr "Content-Type: text/plain; charset=UTF-8\n\n"
 myThreadId >>= forkIO . (threadDelay 500000 >>) . killThread
 case parseExp (unescape . tail . dropWhile (/= '=') $ qstr) of
  ParseOk e -> printeval e `catch` (\e -> print (e :: ErrorCall))
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."
 where unescape ('+':cs) = ' ':unescape cs
       unescape ('%':a:b:cs) = case readHex [a, b] of
        [(x, "")] -> chr x : unescape cs
        _ -> error $ "Failed to parse percent escape: " ++ [a, b]
       unescape (c:cs) = c:unescape cs
       unescape [] = ""

