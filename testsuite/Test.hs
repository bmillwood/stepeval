module Main (main) where

import Control.Applicative
import Control.Exception.Extensible
import Control.Monad
import Data.Generics
import Data.List
import Language.Haskell.Exts
import System.Directory

import Stepeval

main = setCurrentDirectory "testsuite" >> getTests >>= mapM_ runTest

getTests = sort <$> getDirectoryContents "." >>= filterM doesFileExist >>=
 mapM (\t -> ((,) t) <$> readFile t)

runTest (t, b) = handle showEx $ case dropWhile (/= '.') t of
 ".step" -> go . map parseExp $ paragraphs b
 ".eval" -> case map parseExp $ paragraphs b of
  [ParseOk i, ParseOk o]
   | eval ei === o -> success
   | otherwise -> failure (prettyPrint ei) (prettyPrint o)
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
        where a = maybe "Nothing" prettyPrint . squidge $ stepeval e
              b = prettyPrint . squidge $ e'
       go _ = putStrLn $ t ++ ": parse failed!"
       a ==> b = stepeval a === Just b
       a === b = squidge a == squidge b
       paragraphs = foldr p [""] . lines
       p "" bs = "" : bs
       p a ~(b:bs) = (a ++ '\n':b) : bs
       squidge :: GenericT
       squidge = everywhere (mkT deparen `extT` deloc)
       deparen (Paren p) = deparen p
       deparen r = r
       deloc _ = SrcLoc "" 0 0

