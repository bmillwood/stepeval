{-# LANGUAGE RankNTypes #-} -- for anywhereBut
module LambdaCaseLet (eval, itereval, printeval) where

import Control.Applicative ((<$), (<*>))
import Data.Data (Typeable, gmapQ)
import Data.Map (Map, filterWithKey, keys, lookup, insert, delete)
import qualified Data.Map as Map (empty, fromList, null, toList, union)
import Data.Generics (GenericQ,
 everything, everywhereBut, extQ, listify, mkQ, mkT)
import Data.Maybe (fromJust)
import Data.Monoid (Monoid, mappend, mempty, mconcat, Endo (Endo), appEndo)
import qualified Data.Set as Set (empty, fromList, toList, union)
import Prelude hiding (lookup)
import Language.Haskell.Exts (
 Alt (Alt),
 Binds (BDecls),
 Decl (PatBind),
 Exp (App, Case, Con, InfixApp, Lambda, Let, List, Lit, Paren, Var),
 GuardedAlt (GuardedAlt),
 GuardedAlts (UnGuardedAlt, GuardedAlts),
 Literal (Char, Frac, Int, String),
 Pat (PApp, PInfixApp, PList, PLit, PParen, PVar, PWildCard),
 Name (Ident, Symbol),
 QName (Special, UnQual),
 QOp (QConOp, QVarOp),
 Rhs (UnGuardedRhs),
 SpecialCon (Cons),
 SrcLoc (SrcLoc),
 Stmt (Qualifier),
 prettyPrint
 )

(\/) = flip

eval :: Exp -> Exp
eval = last . itereval

itereval :: Exp -> [Exp]
itereval e = e : case stepeval Map.empty e of
 Eval e' -> itereval e'
 _ -> []

stepseval :: Int -> Exp -> Eval
stepseval 0 e = Eval e
stepseval n e = case stepeval Map.empty e of
 Eval e' -> stepseval (n - 1) e'
 r -> r

printeval :: Exp -> IO ()
printeval = mapM_ (putStrLn . prettyPrint) . itereval

-- Force -> might match with further evaluation
data PatternMatch = NoMatch | Force | Match [(Name, Exp)]
data Eval = NoEval | EnvEval (Name, Exp) | Eval Exp deriving Show
type Env = Map Name Exp

liftE :: (Exp -> Exp) -> Eval -> Eval
liftE f (Eval e) = Eval (f e)
liftE _ e = e

orE :: Eval -> Eval -> Eval
orE r@(Eval _) _ = r
orE _ r@(Eval _) = r
orE r _ = r
infixr 3 `orE`

(|$|) = liftE
infix 4 |$|

stepeval :: Env -> Exp -> Eval
stepeval v (Paren p) = stepeval v p
-- These two cases are not really helpful.
stepeval _ (List (x:xs)) = Eval $
 InfixApp x (QConOp (Special Cons)) (List xs)
stepeval _ (Lit (String (x:xs))) = Eval $
 InfixApp (Lit (Char x)) (QConOp (Special Cons)) (Lit (String xs))
stepeval v (Var n) = need v (fromQName n)
stepeval v e@(InfixApp p o q) = case o of
 QVarOp n -> magic v e `orE`
  (\f -> App (App f p) q) |$| need v (fromQName n)
 QConOp _ -> (\p' -> InfixApp p' o q) |$| stepeval v p `orE`
  InfixApp p o |$| stepeval v q
stepeval v e@(App f x) = magic v e `orE` case f of
 Paren p -> stepeval v (App p x)
 Lambda _ [] _ -> error "Lambda with no patterns?"
 Lambda s ps@(p:qs) e -> case patternMatch p x of
  NoMatch -> NoEval
  Force -> App (Paren f) |$| stepeval v x
  Match ms -> case qs of
   [] -> Eval $ applyMatches ms e
   qs
    | anywhere (`elem` newNames) qs -> Eval $ App (Paren newLambda) x
    | otherwise -> Eval . Paren . Lambda s qs $ applyMatches ms e
    where newLambda = Lambda s (fixNames ps) (fixNames e)
          fixNames x = everything (.) (mkQ id (rename <*> newName)) ps x
          rename n n' = everywhereBut (shadows n) (mkT $ renameOne n n')
          renameOne n n' x | x == n = n'
          renameOne _ _ x = x
          newName m@(Ident n)
           | conflicts m = newName . Ident $ n ++ ['\'']
           | otherwise = m
          newName m@(Symbol n)
           | conflicts m = newName . Symbol $ n ++ ['.']
           | otherwise = m
          conflicts n = anywhere (== n) qs || elem n newNames
          newNames =
           Set.toList . foldr (Set.union . Set.fromList) Set.empty .
           map (freeNames . snd) $ ms
 _ -> case stepeval v f of
  Eval g -> Eval $ App g x
  NoEval -> App f |$| stepeval v x
  r -> r
stepeval _ (Case _ []) = error "Case with no branches?"
stepeval v (Case e alts@(Alt l p a (BDecls []) : as)) =
 case patternMatch p e of
  Match rs -> case a of
   UnGuardedAlt x -> Eval (applyMatches rs x)
   GuardedAlts (GuardedAlt m ss x : gs) -> case ss of
    [] -> error "GuardedAlt with no body?"
    [Qualifier (Con (UnQual (Ident s)))]
     | s == "True" -> Eval (applyMatches rs x)
     | s == "False" -> if null gs
       -- no more guards, drop this alt
       then if not (null as) then Eval $ Case e as else NoEval
       -- drop this guard and move to the next
       else Eval $ mkCase (GuardedAlts gs)
     | otherwise -> NoEval
    [Qualifier q] -> mkCase . newAlt |$| stepeval v q
    _ -> error "Unimplemented guarded alt"
    where newAlt q = GuardedAlts (GuardedAlt m [Qualifier q] x : gs)
          mkCase a = Case e (Alt l p a (BDecls []) : as)
   GuardedAlts [] -> error "Case branch with no expression?"
  Force -> Case \/ alts |$| stepeval v e
  NoMatch
   | null as -> NoEval
   | otherwise -> Eval (Case e as)
stepeval _ (Case _ _) = error "Unimplemented case branch"
stepeval _ (Let (BDecls []) e) = Eval e
stepeval v (Let (BDecls bs) e) = let r = stepeval (Map.union newBinds v) e
 in case r of
  NoEval -> NoEval
  Eval e' -> Eval $ relet (cleanBinds e') e'
  EnvEval e' -> maybe r (Eval . (relet \/ e)) $ updateBind e' (cleanBinds e)
 where newBinds = Map.fromList $ map fromLet bs
       cleanBinds e = shedBinds e newBinds
       relet v e
        | Map.null v = e
        | otherwise = Let (BDecls (map reletOne (Map.toList v))) e
       reletOne (n, e) = PatBind (SrcLoc "" 0 0) -- hmm
        (PVar n) Nothing (UnGuardedRhs e) (BDecls [])
       fromLet (PatBind _ (PVar p) Nothing (UnGuardedRhs q) (BDecls [])) =
        (p, q)
       fromLet l = error $ "Unimplemented let binding: " ++ show l
stepeval _ e@(Let _ _) = error $ "Unimplemented let binding: " ++ show e
stepeval _ _ = NoEval

-- this is horrible
magic :: Env -> Exp -> Eval
magic v (App (App (Var p@(UnQual (Symbol "+"))) m) n) =
 case (m, n) of
  (Lit (Int x), Lit (Int y)) -> Eval . Lit . Int $ x + y
  (Lit (Frac x), Lit (Frac y)) -> Eval . Lit . Frac $ x + y
  (Lit _, e) -> InfixApp m (QVarOp p) |$| stepeval v e
  (e, _) -> (\e' -> InfixApp e' (QVarOp p) n) |$| stepeval v e
magic v (InfixApp p (QVarOp o) q) = magic v (App (App (Var o) p) q)
magic _ _ = NoEval

shedBinds :: Exp -> Env -> Env
shedBinds e v = filterWithKey (\k _ -> k `elem` usedKeys) v
 where usedKeys = sb [e] v
       sb es v = let us = usedIn es v in if null us then []
        else us ++ sb (e : map (fromJust . (lookup \/ v)) us) (deletes us v)
       usedIn es v = filter (\k -> any (isFreeIn k) es) (keys v)
       deletes ks = compose (map delete ks)

updateBind :: (Name, Exp) -> Env -> Maybe Env
updateBind (n, e) v = insert n e v <$ lookup n v

need :: Env -> Name -> Eval
need v n = case lookup n v of
 Nothing -> NoEval
 Just e -> case stepeval v e of
  NoEval -> Eval e
  Eval e' -> EnvEval (n, e')
  f -> f

fromQName :: QName -> Name
fromQName (UnQual n) = n
fromQName q = error $ "fromQName: " ++ show q

applyMatches :: [(Name, Exp)] -> Exp -> Exp
applyMatches = compose . map (uncurry replace)

compose :: [a -> a] -> a -> a
compose = appEndo . mconcat . map Endo

isFreeIn :: Name -> Exp -> Bool
isFreeIn n = anywhereBut (shadows n) (mkQ False (== n))

freeNames :: Exp -> [Name]
freeNames e = filter (isFreeIn \/ e) . Set.toList . Set.fromList $
 listify (mkQ False isName) e
 where isName :: Name -> Bool
       isName = const True

instance Monoid PatternMatch where
 mempty = Match []
 mappend _ NoMatch = NoMatch
 mappend _ Force = Force
 mappend NoMatch _ = NoMatch
 mappend Force _ = Force
 mappend (Match f) (Match g) = Match (f ++ g)

patternMatch :: Pat -> Exp -> PatternMatch
-- Strip parentheses
patternMatch (PParen p) x = patternMatch p x
patternMatch p (Paren x) = patternMatch p x
-- Translate infix cases to prefix cases for simplicity
patternMatch (PInfixApp p q r) s = patternMatch (PApp q [p, r]) s
patternMatch p (InfixApp a n b) = case n of
 QVarOp _ -> Force
 QConOp q -> patternMatch p (App (App (Con q) a) b)
-- Patterns that always match
patternMatch (PWildCard) _ = Match []
patternMatch (PVar n) x = Match [(n, x)]
-- Literal match
patternMatch (PLit p) (Lit q)
 | p == q = Match []
 | otherwise = NoMatch
patternMatch (PLit _) _ = Force
patternMatch (PList []) x = case argList x of
 [List []] -> Match []
 [List _] -> NoMatch
 Con _ : _ -> NoMatch
 _ -> Force
-- Lists of patterns
patternMatch (PList (p:ps)) q =
 patternMatch (PApp (Special Cons) [p, PList ps]) q
-- Constructor matches
patternMatch (PApp n ps) q = case argList q of
 (Con c:xs)
  | c == n -> mconcat (zipWith patternMatch ps xs)
  | otherwise -> NoMatch
 _ -> Force
-- Fallback case
patternMatch _ _ = error "Unimplemented pattern match"

argList :: Exp -> [Exp]
argList = reverse . atl
 where atl (App f x) = x : atl f
       atl (InfixApp p o q) = [q, p, case o of
        QVarOp n -> Var n
        QConOp n -> Con n]
       atl e = [e]

replace :: Name -> Exp -> Exp -> Exp
replace n x = everywhereBut (shadows n) (mkT replaceOne)
 where replaceOne (Var (UnQual m)) | m == n = x
       replaceOne e = e

shadows :: Name -> GenericQ Bool
shadows n = mkQ False exprS `extQ` altS
 where exprS (Lambda _ ps _) = anywhere (== PVar n) ps
       exprS (Let (BDecls bs) _) = any letS bs
        where letS (PatBind _ p _ _ _) = anywhere (== PVar n) p
              letS _ = False
       exprS _ = False
       altS (Alt _ p _ _) = anywhere (== PVar n) p

anywhere :: (Typeable a) => (a -> Bool) -> GenericQ Bool
anywhere p = everything (||) (mkQ False p)

-- needs RankNTypes
anywhereBut :: GenericQ Bool -> GenericQ Bool -> GenericQ Bool
anywhereBut p q x = not (p x) && or (q x : gmapQ (anywhereBut p q) x)

