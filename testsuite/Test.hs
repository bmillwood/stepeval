module Main (main) where

import Control.Applicative
import Control.Exception.Extensible
import Control.Monad
import Data.Generics
import Data.List
import Language.Haskell.Exts
import System.Directory
import System.Environment

import Stepeval

main = do
 args <- getArgs
 setCurrentDirectory "testsuite"
 getTests >>= mapM_ (runTest args)

getTests = sort <$> getDirectoryContents "." >>= filterM doesFileExist >>=
 mapM (\t -> ((,) t) <$> readFile t)

runTest args (t, b) = handle showEx $ case dropWhile (/= '.') t of
 ".step" -> go . map parseExp $ paragraphs b
 ".eval" -> case map parseExp $ paragraphs b of
  [ParseOk i, ParseOk o]
   | ei === o -> success
   | otherwise -> failure (output ei) (output o)
   where ei = eval i
  rs -> error $ "unexpected test parse result: " ++ show rs
 _ -> return ()
 where success = putStrLn $ t ++ ": success!"
       failure a b = putStrLn $ t ++ ": failure:\n" ++ a ++ '\n':b
       showEx e = putStrLn $ t ++ ": error: " ++ show (e :: SomeException)
       go [] = error $ t ++ ": empty test?"
       go [_] = success
       go (ParseOk e:r@(ParseOk e'):es)
        | e ==> e' = go (r:es)
        | otherwise = failure a b
        where a = maybe "Nothing" presentable $ stepeval e
              b = presentable e'
              presentable = output . squidge
       go _ = putStrLn $ t ++ ": parse failed!"
       output | verbose = show | otherwise = prettyPrint
       verbose = elem "-v" args || elem "--verbose" args
       a ==> b = maybe False (=== b) (stepeval a)
       a === b = squidge a == squidge b
       paragraphs = foldr p [""] . lines
       p "" bs = "" : bs
       p a ~(b:bs) = (a ++ '\n':b) : bs
       squidge = everywhere (mkT . const $ SrcLoc "" 0 0)

