module Main (cgiMain, cliMain, main) where

import Language.Haskell.Stepeval

import Control.Applicative
import Control.Concurrent
import Control.Exception as E
import Control.Monad
import Data.Char
import Language.Haskell.Exts
import Numeric
import System.Environment
import System.IO
import Text.Printf

version = "stepeval v0.1"

main :: IO ()
main = do
 args <- getArgs
 case args of
  ["--version"] -> putStrLn version
  [] -> do
   e <- lookup "QUERY_STRING" <$> getEnvironment
   case e of
    Nothing -> cliMain
    Just s -> cgiMain s
  _ -> printf "Usage: %s [--version]\n" =<< getProgName

getPrelude :: IO [Decl]
getPrelude = handle (\e -> return [] `const` (e :: SomeException)) $ do
 ParseOk (Module _ _ [] Nothing Nothing [] ds) <- parseFile preludeFile
 return ds

preludeFile :: FilePath
preludeFile = "Prelude.txt"

cliMain :: IO ()
cliMain = do
 putStrLn "Enter a string to parse, terminated by a blank line:"
 exp <- unlines <$> getLines
 prelude <- getPrelude
 case parseExp exp of
  ParseOk e -> forM_ (itereval prelude e) $
   (>> (hFlush stdout >> getLine)) . putStr . prettyPrint
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."
 where getLines :: IO [String]
       getLines = do
        line <- getLine
        if null line then return [] else (line :) <$> getLines

data Step = Finished | Terminated | Error String | Eval Exp

cgiMain :: String -> IO ()
cgiMain qstr = do
 let exp = case dropWhile (/= '=') qstr of
      _ : v -> unescape v
      "" -> ""
 prelude <- getPrelude
 putStr . concat $
  ["Content-Type: text/html; charset=UTF-8\n\n",
   "<html>\n<head>\n",
   "<title>" ++ version ++ "</title>\n",
   "<style type=\"text/css\">\n",
   "ol { white-space: pre; font-family: monospace }\n</style>\n",
   "</head>\n<body>\n",
   "<p><a href=\"http://github.com/bmillwood/stepeval\">",
   "Source</a></p>\n",
   if null prelude then "" else
    "<p><a href=\"" ++ preludeFile ++ "\">Prelude</a></p>\n",
   "<form method=\"get\" action=\"\">\n",
   "<textarea rows=\"5\" cols=\"80\" name=\"expr\">",
   exp,
   "</textarea><br>\n",
   "<input type=\"submit\" value=\"Evaluate!\">\n",
   "</form>\n"]
 myThreadId >>= forkIO . (threadDelay 500000 >>) . killThread
 unless (null exp) $ case parseExp exp of
  ParseOk e -> output prelude e `E.catch` \e -> const
   (putStrLn "Hard time limit expired! This is probably a bug :(")
   (e :: AsyncException)
  ParseFailed _ _ -> putStrLn "Sorry, parsing failed."
 putStrLn "</body>\n</html>"
 where unescape ('+':cs) = ' ':unescape cs
       unescape ('%':a:b:cs) = case readHex [a, b] of
        [(x, "")] -> chr x : unescape cs
        _ -> error $ "Failed to parse percent escape: " ++ [a, b]
       unescape (c:cs) = c:unescape cs
       unescape [] = ""
       output prelude e = do
        eval <- newEmptyMVar
        forkIO $ (mapM_ (putMVar eval . Eval) (itereval prelude e) >>
         putMVar eval Finished) `E.catch`
         (\(ErrorCall s) -> putMVar eval (Error s))
        forkIO $ threadDelay 250000 >> putMVar eval Terminated
        putStrLn "<ol>"
        outputOne eval
        putStrLn "</ol>"
       outputOne eval = do
        next <- takeMVar eval
        case next of
         Finished -> return ()
         Terminated -> putStrLn $ "<li>Time limit expired!</li>"
         Error s -> putStrLn $ "<li>" ++ s ++ "</li>"
         Eval e -> putStrLn ("<li>" ++ pp e ++ "</li>") >> outputOne eval
          where pp = concatMap escape . prettyPrint
       escape '&' = "&amp;"
       escape '<' = "&lt;"
       escape '>' = "&gt;"
       escape c = [c]

