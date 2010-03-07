{-# LANGUAGE RankNTypes #-}
module LambdaCaseLet (eval, itereval, printeval, stepeval, stepseval) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad ((<=<), join)
import Data.Data (Typeable, gmapQ, gmapT)
import Data.List (delete, find, partition, unfoldr)
import Data.Maybe (fromMaybe)
import Data.Monoid (mconcat, Endo (Endo, appEndo))
import Data.Generics (GenericQ, GenericT,
 everything, everywhereBut, extQ, extT, listify, mkQ, mkT)
import qualified Data.Set as Set (fromList, toList)
import Language.Haskell.Exts (
 Alt (Alt),
 Binds (BDecls),
 Decl (PatBind),
 Exp (App, Case, Con, Do, If, InfixApp, Lambda, LeftSection,
  Let, List, Lit, Paren, RightSection, Var),
 GuardedAlt (GuardedAlt),
 GuardedAlts (UnGuardedAlt, GuardedAlts),
 Literal (Char, Frac, Int, String),
 Pat (PApp, PInfixApp, PList, PLit, PParen, PVar, PWildCard),
 Name (Ident, Symbol),
 QName (Special, UnQual),
 QOp (QConOp, QVarOp),
 Rhs (UnGuardedRhs),
 SpecialCon (Cons),
 Stmt (Generator, LetStmt, Qualifier),
 prettyPrint
 )

eval :: Exp -> Exp
eval = last . itereval

printeval :: Exp -> IO ()
printeval = mapM_ (putStrLn . prettyPrint) . itereval

itereval :: Exp -> [Exp]
itereval e = e : unfoldr (fmap (join (,)) . stepeval) e

stepseval :: Int -> Exp -> Maybe Exp
stepseval n = foldr (<=<) return $ replicate n stepeval

stepeval :: Exp -> Maybe Exp
stepeval e = case step [] e of
 Step (Eval e') -> Just e'
 _ -> Nothing

-- Sometimes evaluating a subexpression means evaluating an outer expression
data Eval = EnvEval Decl | Eval Exp
 deriving Show
data EvalStep = Failure | Done | Step Eval
 deriving Show
type MatchResult = Either Eval [(Name, Exp)]
type Env = [Decl]

liftE :: (Exp -> Exp) -> EvalStep -> EvalStep
liftE f (Step (Eval e)) = Step (Eval (f e))
liftE _ e = e

orE :: EvalStep -> EvalStep -> EvalStep
orE r@(Step _) _ = r
orE _ r@(Step _) = r
orE r _ = r
infixr 3 `orE`

(|$|) = liftE
infix 4 |$|

yield :: Exp -> EvalStep
yield = Step . Eval

step :: Env -> Exp -> EvalStep
step v (Paren p) = step v p
step _ (List (x:xs)) = yield $
 InfixApp x (QConOp (Special Cons)) (List xs)
step _ (Lit (String (x:xs))) = yield $
 InfixApp (Lit (Char x)) (QConOp (Special Cons)) (Lit (String xs))
step _ (Do []) = error "Empty do?"
step _ (Do [Qualifier e]) = yield e
step _ (Do [e]) = error $
 "Last statement in a do block must be an expression: " ++ show e
step _ (Do (s:ss)) = case s of
 Qualifier e -> yield $ InfixApp e (op ">>") (Do ss)
 Generator s p e -> yield $ InfixApp e (op ">>=")
  (Lambda s [p] (Do ss))
 LetStmt bs -> yield $ Let bs (Do ss)
 s -> todo s
 where op = QVarOp . UnQual . Symbol
step v (Var n) = need v (fromQName n)
step _ (If (Con (UnQual (Ident i))) t f) = case i of
 "True" -> yield t
 "False" -> yield f
 _ -> Failure
step v (If e t f) = (\e -> If e t f) |$| step v e
step v e@(InfixApp p o q) = case o of
 QVarOp n -> magic v e `orE`
  (\f -> App (App f p) q) |$| need v (fromQName n)
 QConOp _ -> (\p' -> InfixApp p' o q) |$| step v p `orE`
  InfixApp p o |$| step v q
step v e@(App f x) = magic v e `orE` case f of
 Paren p -> step v (App p x)
 Lambda _ [] _ -> error "Lambda with no patterns?"
 Lambda s ps@(p:qs) e -> case patternMatch v p x of
  Nothing -> Failure
  Just (Left r) -> App (Lambda s ps e) |$| Step r
  Just (Right ms) -> case qs of
   [] -> yield $ applyMatches ms e
   qs
    | anywhere (`elem` mnames) qs -> yield $ App newLambda x
    | otherwise -> yield . Lambda s qs $ applyMatches ms e
    where newLambda = Lambda s (fixNames ps) (fixNames e)
          fixNames :: GenericT -- the DMR strikes again
          -- The first pattern in the lambda is about to be gobbled. Rename
          -- every other pattern that will conflict with any of the names
          -- introduced by the pattern match.
          -- We avoid names already existing in the lambda, except for the
          -- one we're in the process of renaming (that would be silly)
          fixNames = appEndo . mconcat $
           map (\n -> Endo $ alpha n (delete n lnames ++ mnames))
           (freeNames qs)
          lnames = freeNames ps ++ freeNames e
          mnames = Set.toList . mconcat . map Set.fromList $
           map (freeNames . snd) ms
 LeftSection e o -> yield $ InfixApp e o x
 RightSection o e -> yield $ InfixApp x o e
 _ -> case step v f of
  Step (Eval g) -> yield $ App g x
  Done -> App f |$| step v x
  r -> r
step _ (Case _ []) = error "Case with no branches?"
step v (Case e alts@(Alt l p a (BDecls []) : as)) =
 case patternMatch v p e of
  Just (Right rs) -> case a of
   UnGuardedAlt x -> yield (applyMatches rs x)
   GuardedAlts (GuardedAlt m ss x : gs) -> case ss of
    [] -> error "GuardedAlt with no body?"
    [Qualifier (Con (UnQual (Ident s)))]
     | s == "True" -> yield (applyMatches rs x)
     | s == "False" -> if null gs
       -- no more guards, drop this alt
       then if not (null as) then yield $ Case e as else Failure
       -- drop this guard and move to the next
       else yield $ mkCase (GuardedAlts gs)
     | otherwise -> Failure
    [Qualifier q] -> mkCase . newAlt |$| step v q
    a -> todo a
    where newAlt q = GuardedAlts (GuardedAlt m [Qualifier q] x : gs)
          mkCase a = Case e (Alt l p a (BDecls []) : as)
   GuardedAlts [] -> error "Case branch with no expression?"
  Just (Left e) -> case e of
   Eval e' -> yield $ Case e' alts
   r -> Step r
  Nothing
   | null as -> Failure
   | otherwise -> yield $ Case e as
step _ e@(Case _ _) = todo e
step _ (Let (BDecls []) e) = yield e
step v (Let (BDecls bs) e) = case step (bs ++ v) e of
  Step (Eval e') -> yield $ newLet e' bs
  Step r@(EnvEval e') -> Step $ maybe r (Eval . newLet e) $ updateBind e' bs
  r -> r
 where newLet e bs = case tidyBinds e bs of
        [] -> e
        bs' -> Let (BDecls bs') e
step _ (LeftSection _ _) = Done
step _ (RightSection _ _) = Done
step _ (Lit _) = Done
step _ (List []) = Done
step _ (Con _) = Done
step _ (Lambda _ _ _) = Done
step _ e = todo e

-- This code isn't very nice, largely because I anticipate it all being
-- replaced eventually anyway.
magic :: Env -> Exp -> EvalStep
magic v e = case e of
 App (App (Var p) x) y -> rhs (fromQName p) x y
 InfixApp x (QVarOp o) y -> rhs (fromQName o) x y
 _ -> Done
 where rhs p@(Symbol s) x y = case lookup s ops of
        Just (+*) -> case (step v x, step v y) of
         (Done, Done) -> x +* y
         (Done, y') -> InfixApp x op |$| y'
         (x', _) -> (\e -> InfixApp e op y) |$| x'
         where op = QVarOp (UnQual p)
        Nothing -> Done
       rhs _ _ _ = Done
       lit x = case properFraction (toRational x) of
        (i, 0) -> Lit (Int i)
        (i, r) -> Lit (Frac (toRational i + r))
       con = Con . UnQual . Ident
       unlit (Lit (Int i)) = Just $ toRational i
       unlit (Lit (Frac r)) = Just r
       unlit _ = Nothing
       ops = [
        ("+", num (+)),
        ("*", num (*)),
        ("-", num (-)),
        ("<", bool (<)),
        ("<=", bool (<=)),
        (">", bool (>)),
        (">=", bool (>=)),
        ("==", bool (==)),
        ("/=", bool (/=))]
       num op = mkOp lit op
       bool op = mkOp (con . show) op
       mkOp f g m n = maybe Done (yield . f) $ g <$> unlit m <*> unlit n

tidyBinds :: Exp -> Env -> Env
tidyBinds e v = let keep = go [e] v in filter (`elem` keep) v
 where go es ds = let (ys, xs) = partition (usedIn es) ds
        in if null ys then [] else ys ++ go (concatMap exprs ys) xs
       binds (PatBind _ (PVar n) _ _ _) = [n]
       binds l = todo l
       exprs (PatBind _ _ _ (UnGuardedRhs e) _) = [e]
       exprs l = todo l
       usedIn es d = any (\n -> any (isFreeIn n) es) (binds d)

updateBind :: Decl -> Env -> Maybe Env
updateBind p@(PatBind _ (PVar n) _ _ _) v = case break match v of
 (_, []) -> Nothing
 (h, _ : t) -> Just $ h ++ p : t
 where match (PatBind _ (PVar m) _ _ _) = n == m
       match _ = False
updateBind l _ = todo l

need :: Env -> Name -> EvalStep
need v n = case envLookup v n of
 Nothing -> Done
 Just b@(PatBind s (PVar n) t (UnGuardedRhs e) (BDecls [])) ->
  case step (delete b v) e of
   Done -> yield e
   Step (Eval e') -> Step . EnvEval $
    PatBind s (PVar n) t (UnGuardedRhs e') (BDecls [])
   f -> f
 Just l -> todo l

envLookup :: Env -> Name -> Maybe Decl
envLookup v n = find match v
 where match (PatBind _ (PVar m) _ _ _) = m == n
       match l = todo l

fromQName :: QName -> Name
fromQName (UnQual n) = n
fromQName q = error $ "fromQName: " ++ show q

applyMatches :: [(Name, Exp)] -> GenericT
-- If it's not an Exp, just recurse into it, otherwise try to substitute...
applyMatches ms x = recurse `extT` replaceOne $ x
 where replaceOne e@(Var (UnQual m)) = fromMaybe e $ lookup m ms
       -- ...or else recurse anyway
       replaceOne e = recurse e
       recurse e = gmapT (applyMatches (notShadowed e)) e
       -- Parameter here might be redundant - it's only called on x anyway
       notShadowed e = filter (not . flip shadows e . fst) ms

alpha :: Name -> [Name] -> GenericT
alpha n avoid =
 -- note infinite list, so find cannot give Nothing
 let Just m = find (`notElem` avoid)
      (n : map (\i -> withName (++ show i) n) [1 ..])
  in everywhereBut (shadows n) (mkT $ replaceOne n m)
 where replaceOne :: Name -> Name -> Name -> Name
       replaceOne n m r | n == r = m
       replaceOne _ _ r = r

withName :: (String -> String) -> Name -> Name
withName f (Ident n) = Ident (f n)
withName f (Symbol n) = Symbol (f n)

isFreeIn :: Name -> GenericQ Bool
isFreeIn n = anywhereBut (shadows n) (is n)
 where is n@(Symbol s)
        | s == ">>" || s == ">>=" = mkQ False (== n) `extQ` isDo
       is n = mkQ False (== n)
       isDo (Do _) = True
       isDo _ = False

freeNames :: GenericQ [Name]
freeNames e = filter (`isFreeIn` e) . Set.toList . Set.fromList $
 listify (mkQ False isName) e
 where isName :: Name -> Bool
       isName = const True

peval :: EvalStep -> Maybe MatchResult
peval (Step e) = Just $ Left e
peval _ = Nothing

pmatch :: [(Name, Exp)] -> Maybe MatchResult
pmatch = Just . Right

patternMatch :: Env -> Pat -> Exp -> Maybe MatchResult
-- Strip parentheses
patternMatch v (PParen p) x = patternMatch v p x
patternMatch v p (Paren x) = patternMatch v p x
-- Patterns that always match
patternMatch _ (PWildCard) _ = pmatch []
patternMatch _ (PVar n) x = pmatch [(n, x)]
-- Variables will need to be substituted if they still haven't matched
patternMatch v p (Var q) = case envLookup v (fromQName q) of
 Nothing -> Nothing
 Just (PatBind _ _ _ (UnGuardedRhs e) _) -> patternMatch v p e
 Just l -> todo l
-- Translate infix cases to prefix cases for simplicity
-- I need to stop doing this at some point
patternMatch v (PInfixApp p q r) s = patternMatch v (PApp q [p, r]) s
patternMatch v p (InfixApp a n b) = case n of
 QVarOp n -> peval $ need v (fromQName n)
 QConOp q -> patternMatch v p (App (App (Con q) a) b)
-- Literal match
patternMatch _ (PLit p) (Lit q)
 | p == q = pmatch []
 | otherwise = Nothing
patternMatch v (PLit _) s = peval $ step v s
patternMatch v (PList []) x = case argList x of
 [List []] -> pmatch []
 [List _] -> Nothing
 Con _ : _ -> Nothing
 _ -> peval $ step v x
-- Lists of patterns
patternMatch v (PList (p:ps)) q =
 patternMatch v (PApp (Special Cons) [p, PList ps]) q
-- Constructor matches
patternMatch v (PApp n ps) q = case argList q of
 (Con c:xs)
  | c == n -> matches ps xs
  | otherwise -> Nothing
  where matches [] [] = pmatch []
        matches (p:ps) (x:xs) = case (patternMatch v p x, matches ps xs) of
         (Nothing, _) -> Nothing
         (r@(Just (Left _)), _) -> r
         (Just (Right xs), Just (Right ys)) -> Just (Right (xs ++ ys))
         (_, r) -> r
        matches _ _ = Nothing
 _ -> peval $ step v q
-- Fallback case
patternMatch _ p q = todo (p, q)

argList :: Exp -> [Exp]
argList = reverse . atl
 where atl (App f x) = x : atl f
       atl (InfixApp p o q) = [q, p, case o of
        QVarOp n -> Var n
        QConOp n -> Con n]
       atl e = [e]

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
anywhereBut p q x = not (p x) && (q x || (or $ gmapQ (anywhereBut p q) x))

todo :: (Show s) => s -> a
todo = error . ("Not implemented: " ++) . show

