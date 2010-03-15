module Stepeval (eval, itereval, printeval, stepeval, stepseval) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad ((<=<), join, replicateM)
import Data.Data (Typeable, gmapQ, gmapT)
import Data.Foldable (foldMap)
import Data.List (delete, find, partition, unfoldr)
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo (Endo, appEndo))
import Data.Generics (GenericQ, GenericT,
 everything, everywhereBut, extQ, extT, listify, mkQ, mkT)
import qualified Data.Set as Set (fromList, toList)
import Language.Haskell.Exts (
 Alt (Alt),
 Binds (BDecls),
 Decl (PatBind, FunBind),
 Exp (App, Case, Con, Do, If, InfixApp, Lambda, LeftSection,
  Let, List, Lit, Paren, RightSection, Tuple, Var),
 GuardedAlt (GuardedAlt),
 GuardedAlts (UnGuardedAlt, GuardedAlts),
 GuardedRhs (GuardedRhs),
 Literal (Char, Frac, Int, String),
 Match (Match),
 Pat (PApp, PInfixApp, PList, PLit, PParen, PTuple, PVar, PWildCard),
 Name (Ident, Symbol),
 QName (Special, UnQual),
 QOp (QConOp, QVarOp),
 Rhs (UnGuardedRhs, GuardedRhss),
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
type Scope = [Decl]
type Env = [Scope]

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
 s -> todo "step Do" s
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
step v e@(App _ _) = magic v e `orE` case argList e of
 LeftSection e o : x : xs -> yield . unArgList $ InfixApp e o x : xs
 RightSection o e : x : xs -> yield . unArgList $ InfixApp x o e : xs
 f@(Lambda _ _ _) : es -> applyLambda f es
  where applyLambda (Lambda _ [] _) _ = error "Lambda with no patterns?"
        applyLambda f [] = yield f
        applyLambda (Lambda s ps@(p:qs) e) (x:xs) =
         case patternMatch v p x of
          Nothing -> Failure
          Just (Left r) ->
           (\x -> unArgList $ Lambda s ps e : x : xs) |$| Step r
          Just (Right ms) -> case qs of
           [] -> yield $ unArgList (applyMatches ms e : xs)
           qs
            | anywhere (`elem` mnames) qs ->
               yield . unArgList $ newLambda : x : xs
            | otherwise -> applyLambda (Lambda s qs $ applyMatches ms e) xs
            where newLambda = Lambda s (fixNames ps) (fixNames e)
                  fixNames :: GenericT -- the DMR strikes again
                  -- The first pattern in the lambda is about to be gobbled.
                  -- Rename every other pattern that will conflict with any
                  -- of the names introduced by the pattern match.
                  -- We avoid names already existing in the lambda, except
                  -- for the one we're in the process of renaming (that
                  -- would be silly)
                  fixNames = appEndo $ foldMap
                   (\n -> Endo $ alpha n (delete n lnames ++ mnames))
                   (freeNames qs)
                  lnames = freeNames ps ++ freeNames e
                  mnames = Set.toList .
                   foldMap (Set.fromList . freeNames . snd) $ ms
        applyLambda _ _ = error "not a lambda!"
 es -> liststep v unArgList es
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
    a -> todo "step Case GuardedAlts" a
    where newAlt q = GuardedAlts (GuardedAlt m [Qualifier q] x : gs)
          mkCase a = Case e (Alt l p a (BDecls []) : as)
   GuardedAlts [] -> error "Case branch with no expression?"
  Just (Left e) -> case e of
   Eval e' -> yield $ Case e' alts
   r -> Step r
  Nothing
   | null as -> Failure
   | otherwise -> yield $ Case e as
step _ e@(Case _ _) = todo "step Case" e
step _ (Let (BDecls []) e) = yield e
step v (Let (BDecls bs) e) = case step (bs : v) e of
  Step (Eval e') -> yield $ newLet e' bs
  Step r@(EnvEval e') -> Step $ maybe r (Eval . newLet e) $ updateBind e' bs
  r -> r
 where newLet e bs = case tidyBinds e bs of
        [] -> e
        bs' -> Let (BDecls bs') e
step v (Tuple xs) = case xs of
 [] -> error "Empty tuple?"
 [_] -> error "Singleton tuple?"
 es -> liststep v Tuple es
step _ (LeftSection _ _) = Done
step _ (RightSection _ _) = Done
step _ (Lit _) = Done
step _ (List []) = Done
step _ (Con _) = Done
step _ (Lambda _ _ _) = Done
step _ e = todo "step _" e

liststep :: Env -> ([Exp] -> Exp) -> [Exp] -> EvalStep
liststep v f es = go es id
 where go es g = case es of
        [] -> Done
        e:es -> case step v e of
          Step (Eval e') -> yield . f . g $ e':es
          Done -> go es (g . (e:))
          r -> r

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

tidyBinds :: Exp -> Scope -> Scope
tidyBinds e v = let keep = go (usedIn e) v in filter (`elem` keep) v
 where go p ds = case partition p ds of
        ([], _) -> []
        (ys, xs) -> ys ++ go ((||) <$> p <*> usedIn ys) xs
       binds (PatBind _ (PVar n) _ _ _) = [n]
       binds (FunBind ms) = [funName ms]
       binds l = todo "tidyBinds binds" l
       usedIn es d = any (\n -> isFreeIn n es) (binds d)

need :: Env -> Name -> EvalStep
need v n = case envBreak match v of
 (_, _, [], _) -> Done
 (_, bs, c : cs, ds) -> case c of
  PatBind s (PVar n) t (UnGuardedRhs e) (BDecls []) ->
   case step ((bs ++ cs) : ds) e of
    Done -> yield e
    Step (Eval e') -> Step . EnvEval $
     PatBind s (PVar n) t (UnGuardedRhs e') (BDecls [])
    f -> f
  FunBind ms -> yield $ funToCase ms
  b -> todo "need case" b
 where match (PatBind _ (PVar m) _ _ _) = m == n
       match (FunBind ms) = funName ms == n
       match l = todo "need match" l

funName :: [Match] -> Name
funName [] = error "No matches?"
funName (Match _ n _ _ _ _ : ms) = foldr match n ms
 where match (Match _ m _ _ _ _) n | m == n = n
       match m n = error $ "Match names don't? " ++ show (m, n)

funToCase :: [Match] -> Exp
funToCase [] = error "No matches?"
-- unsure of whether this is the right SrcLoc
funToCase [Match s _ ps _ (UnGuardedRhs e) (BDecls [])] = Lambda s ps e
funToCase ms@(Match s _ ps _ _ _ : _) = Lambda s qs $ Case e as
 where qs = map (PVar . Ident) names
       e = tuple $ map (Var . UnQual . Ident) names
       as = map matchToAlt ms
       tuple [] = error "No patterns in match?"
       tuple [x] = x
       tuple xs = Tuple xs
       names = zipWith const (concatMap (\i -> nameslen i) [1 ..]) ps
       nameslen i = replicateM i ['a' .. 'z']
       matchToAlt (Match s _ ps _ r bs) = Alt s (ptuple ps) (rhsToAlt r) bs
       ptuple [] = error "No patterns in match?"
       ptuple [x] = x
       ptuple xs = PTuple xs
       rhsToAlt (UnGuardedRhs e) = UnGuardedAlt e
       rhsToAlt (GuardedRhss rs) = GuardedAlts $
        map (\(GuardedRhs s t e) -> GuardedAlt s t e) rs

updateBind :: Decl -> Scope -> Maybe Scope
updateBind p@(PatBind _ (PVar n) _ _ _) v = case break match v of
 (_, []) -> Nothing
 (h, _ : t) -> Just $ h ++ p : t
 where match (PatBind _ (PVar m) _ _ _) = n == m
       match _ = False
updateBind l _ = todo "updateBind" l

envLookup :: Env -> Name -> Maybe Decl
envLookup v n = case envBreak match v of
 (_, _, [], _) -> Nothing
 (_, _, c : _, _) -> Just c
 where match (PatBind _ (PVar m) _ _ _) = m == n
       match l = todo "envLookup match" l

envBreak :: (a -> Bool) -> [[a]] -> ([[a]], [a], [a], [[a]])
envBreak _ [] = ([], [], [], [])
envBreak p (x:xs) = case break p x of
 (_, []) -> (x:as, bs, cs, ds)
 (ys, zs) -> ([], ys, zs, xs)
 where (as, bs, cs, ds) = envBreak p xs

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
isFreeIn n x = not (shadows n x) && (is n x || or (gmapQ (isFreeIn n) x))
 where is n@(Symbol s)
        | s == ">>" || s == ">>=" = mkQ False (== n) `extQ` isDo
       is n = mkQ False (== n)
       isDo (Do _) = True
       isDo _ = False

freeNames :: GenericQ [Name]
freeNames e = filter (`isFreeIn` e) . Set.toList . Set.fromList $
 listify (const True) e

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
 Just l -> todo "patternMatch Var" l
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
-- Tuples
patternMatch v (PTuple ps) q = case q of
 Tuple qs -> matches v ps qs Tuple
 _ -> peval $ step v q
-- Constructor matches
patternMatch v (PApp n ps) q = case argList q of
 (Con c:xs)
  | c == n -> matches v ps xs (unArgList . (Con c :))
  | otherwise -> Nothing
 _ -> peval $ step v q
-- Fallback case
patternMatch _ p q = todo "patternMatch _" (p, q)

matches :: Env -> [Pat] -> [Exp] -> ([Exp] -> Exp) -> Maybe MatchResult
matches _ [] [] _ = pmatch []
matches v ps xs f = go v ps xs id
 where go _ [] [] _ = pmatch []
       go v (p:ps) (e:es) g =
        case (patternMatch v p e, go v ps es (g . (e:))) of
         (Nothing, _) -> Nothing
         (Just (Left (Eval e')), _) -> Just . Left . Eval . f . g $ e' : es
         (r@(Just (Left _)), _) -> r
         (Just (Right xs), Just (Right ys)) -> Just (Right (xs ++ ys))
         (_, r) -> r
       go _ _ _ _ = Nothing

argList :: Exp -> [Exp]
argList = reverse . atl
 where atl (App f x) = x : atl f
       atl (Paren p) = atl p
       atl (InfixApp p o q) = [q, p, case o of
        QVarOp n -> Var n
        QConOp n -> Con n]
       atl e = [e]

unArgList :: [Exp] -> Exp
unArgList (e:es@(x:ys)) = case e of
 Con q@(Special Cons) -> rhs (QConOp q) x ys
 Con q@(UnQual (Symbol _)) -> rhs (QConOp q) x ys
 Var q@(UnQual (Symbol _)) -> rhs (QVarOp q) x ys
 e -> foldl App e es
 where rhs o x [] = LeftSection x o
       rhs o x (y:ys) = unArgList $ InfixApp x o y : ys
unArgList (e:es) = foldl App e es
unArgList [] = error "unArgList: no expressions"

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

todo :: (Show s) => String -> s -> a
todo s = error . (s ++) . (": Not implemented: " ++) . show

