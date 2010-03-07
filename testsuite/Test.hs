module Main (main) where

import Control.Monad
import Data.Functor
import Data.Generics
import Data.List
import Language.Haskell.Exts
import System.Directory

import LambdaCaseLet

main = setCurrentDirectory "testsuite" >> getTests >>= mapM_ runTest

getTests = sort <$> getDirectoryContents "." >>= filterM doesFileExist >>=
 mapM (\t -> ((,) t) <$> readFile t)

runTest (t, b) = case dropWhile (/= '.') t of
 ".step" -> go . map parseExp $ paragraphs b
 ".eval" -> case map parseExp $ paragraphs b of
  [ParseOk i, ParseOk o] ->
   let ei = eval i in if eval ei === o then success else failure ei o
 _ -> return ()
 where success = putStrLn $ t ++ ": success!"
       failure a b = putStrLn $ t ++ ": failure:\n" ++ show a ++ '\n':show b
       go [] = error $ t ++ ": empty test?"
       go [_] = success
       go (ParseOk e:r@(ParseOk e'):es)
        | e ==> e' = go (r:es)
        | otherwise = failure (squidge (stepeval e)) (squidge e')
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

