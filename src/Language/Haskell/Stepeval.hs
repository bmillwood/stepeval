module Language.Haskell.Stepeval (Scope, eval, itereval, printeval, stepeval) where

import Control.Arrow (first)
import Control.Applicative ((<$), (<$>), (<*>), (<|>))
import Control.Monad (guard, join, replicateM)
import Data.Foldable (foldMap)
import Data.List (delete, find, partition, unfoldr)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Endo (Endo, appEndo))
import Data.Generics (Data, Typeable,
  everything, everywhereBut, extQ, extT, gmapQ, gmapT, listify, mkQ, mkT)
import qualified Data.Set as Set (fromList, toList)

import Language.Haskell.Exts (
  Alt (Alt),
  Binds (BDecls), Boxed (Boxed), Decl (PatBind, FunBind, InfixDecl),
  Exp (App, Case, Con, Do, If, InfixApp, Lambda, LeftSection,
    Let, List, Lit, Paren, RightSection, Tuple, TupleSection, Var),
  GuardedAlt (GuardedAlt), GuardedAlts (UnGuardedAlt, GuardedAlts),
  Literal (Char, Frac, Int, String),
  Match (Match),
  Op (ConOp, VarOp),
  Pat (PApp, PAsPat, PInfixApp, PList, PLit, PParen, PTuple, PVar,
    PWildCard),
  Name (Ident, Symbol), QName (Special, Qual, UnQual), QOp (QConOp, QVarOp),
  Rhs (UnGuardedRhs),
  SpecialCon (Cons, TupleCon),
  SrcLoc (), -- (SrcLoc),
  Stmt (Generator, LetStmt, Qualifier),
  preludeFixities, prettyPrint)

import Parenthise (deparen, enparenWith, scopeToFixities)

-- | Evaluate an expression as completely as possible.
eval :: Scope -> Exp -> Exp
eval s = last . itereval s

-- | Print each step of the evaluation of an expression.
printeval :: Scope -> Exp -> IO ()
printeval s = mapM_ (putStrLn . prettyPrint) . itereval s

-- | Make a list of the evaluation steps of an expression.
-- Note that @head (itereval s exp) == exp@
itereval :: Scope -> Exp -> [Exp]
itereval s e = e : unfoldr (fmap (join (,)) . stepeval s) e

-- The use of preludeFixities here is questionable, since we don't use
-- prelude functions, but it's more convenient in general.
-- When we grow a proper Prelude of our own, it would be nice to use that
-- instead.
-- | Evaluate an expression by a single step, or give 'Nothing' if the
-- evaluation failed (either because an error ocurred, or the expression was
-- already as evaluated as possible)
stepeval :: Scope -> Exp -> Maybe Exp
stepeval s e = case step [s] e of
  Step (Eval e') -> Just (enparenWith fixes . deparen $ e')
  _ -> Nothing
 where
  fixes = scopeToFixities s ++ preludeFixities

data Eval = EnvEval Decl | Eval Exp
  deriving Show
data EvalStep = Failure | Done | Step Eval
  deriving Show
data PatternMatch = NoMatch | MatchEval Eval | Matched [MatchResult]
  deriving Show
-- | The result of a successful pattern match. The third field is meant to
-- put the 'Exp' that was matched back into the context it came from, e.g.
-- if you matched @[a,b,c]@ against @[1,2,3]@ then one of the 'MatchResult's
-- would be approximately @'MatchResult' \"b\" 2 (\x -> [1,x,3])@
data MatchResult = MatchResult {
  mrName :: Name,
  mrExp :: Exp,
  mrFunc :: (Exp -> Exp) }
type Scope = [Decl]
type Env = [Scope]

-- Involves an evil hack, but only useful for debugging anyway.
instance Show MatchResult where
  showsPrec p (MatchResult n e f) = showParen (p >= 11) $
    showString "MatchResult " . showN . sp . showE . sp . showF
   where
    sp = showString " "
    showN = showsPrec 11 n
    showE = showsPrec 11 e
    -- We assume a sensible function would not produce variables with
    -- empty names
    showF = showParen True $ showString "\\arg -> " . fixVar .
      shows (f (Var (UnQual (Ident ""))))
    -- Find and replace all instances of the empty variable with 'arg'
    fixVar s = case break (`elem` "(V") s of
      (r, "") -> r
      (r, '(':s') -> r ++ dropEq s' "Var (UnQual (Ident \"\")))" ('(':)
      (r, 'V':s') -> r ++ dropEq s' "ar (UnQual (Ident \"\"))" ('V':)
      _ -> error "MatchResult.Show: hack a splode"
    dropEq s "" _ = "arg" ++ fixVar s
    dropEq (x:xs) (d:ds) f
      | x == d = dropEq xs ds (f . (x:))
    dropEq s _ f = f (fixVar s)

-- | Map over e in @'Step' ('Eval' e)@
liftE :: (Exp -> Exp) -> EvalStep -> EvalStep
liftE f (Step (Eval e)) = Step (Eval (f e))
liftE _ e = e

-- | If either argument is a 'Step', return it, otherwise return the first.
orE :: EvalStep -> EvalStep -> EvalStep
orE r@(Step _) _ = r
orE _ r@(Step _) = r
orE r _ = r
infixr 3 `orE`

-- | Infix liftE.
(|$|) :: (Exp -> Exp) -> EvalStep -> EvalStep
(|$|) = liftE
infix 4 |$|

-- | @'Step' . 'Eval'@
yield :: Exp -> EvalStep
yield = Step . Eval

-- | The basic workhorse of the module - step the given expression in the
-- given environment.
step :: Env -> Exp -> EvalStep

-- Variables
step v (Var n) = need v (fromQName n)

-- Function application
step v e@(App f x) = magic v e `orE` case argList e of
  LeftSection e o : x : xs -> yield $ unArgList (InfixApp e o x) xs
  RightSection o e : x : xs -> yield $ unArgList (InfixApp x o e) xs
  f@(TupleSection _) : xs -> yield $ unArgList f xs
  f@(Con (Special (TupleCon _ _))) : xs -> yield $ unArgList f xs
  -- note that since we matched against an App, es should be non-empty
  Lambda s ps e : es -> applyLambda s ps e es
   where
    applyLambda _ [] _ _ = error "Lambda with no patterns?"
    applyLambda s ps e [] = yield $ Lambda s ps e
    applyLambda s ps@(p:qs) e (x:xs) = case patternMatch v p x of
      NoMatch -> Failure
      MatchEval r -> (\x -> unArgList (Lambda s ps e) $ x : xs) |$| Step r
      Matched ms -> case qs of
        [] -> yield $ unArgList (applyMatches ms e) xs
        qs
          | anywhere (`elem` mnames) qs ->
            yield . unArgList newLambda $ x : xs
          | otherwise -> applyLambda s qs (applyMatches ms e) xs
         where
          newLambda = Lambda s (fixNames ps) (fixNames e)
          fixNames :: Data a => a -> a -- the DMR strikes again
          -- The first pattern in the lambda is about to be gobbled.
          -- Rename every other pattern that will conflict with any of the
          -- names introduced by the pattern match. We avoid names already
          -- existing in the lambda, except for the one we're in the process
          -- of renaming (that would be silly)
          fixNames = appEndo $ foldMap
            (\n -> Endo $ alpha n (delete n lnames ++ mnames))
            (freeNames qs)
          lnames = freeNames ps ++ freeNames e
          mnames = Set.toList . foldMap (Set.fromList . freeNames . mrExp)
            $ ms
  f@(Var q) : es -> case envLookup v (fromQName q) of
    Nothing -> Done
    Just (PatBind _ _ _ _ _) -> (\f' -> unArgList f' es) |$| step v f
    Just (FunBind ms)
      | null . drop (pred arity) $ es -> fallback
      | otherwise -> foldr (orE . app) fallback ms
       where
        arity = funArity ms
        (xs, r) = splitAt arity es
        app (Match _ _ ps _ (UnGuardedRhs e') (BDecls ds)) =
          case matches v ps xs (unArgList f) of
            NoMatch -> Failure
            MatchEval (Eval e') -> yield $ unArgList e' r
            MatchEval e -> Step e
            Matched ms -> yield . applyMatches ms . mkLet ds $
              unArgList e' r
        app m = todo "step App Var app" m
    Just d -> todo "step App Var" d
  l@(Let (BDecls bs) f) : e : es ->
    foldr (orE . alphaBind) fallback incomingNames
   where
    incomingNames = freeNames e
    avoidNames = incomingNames ++ freeNames f
    alphaBind n
      | shadows n l = flip unArgList (e : es) |$|
        yield (uncurry mkLet (alpha n avoidNames (tidyBinds f bs, f)))
      | otherwise = yield $ unArgList (Let (BDecls bs) (App f e)) es
  _ -> fallback
 where
  fallback = flip app x |$| step v f `orE` app f |$| step v x
step v e@(InfixApp p o q) = case o of
  QVarOp n -> magic v e `orE`
    step v (App (App (Var n) p) q)
  QConOp _ -> (\p' -> InfixApp p' o q) |$| step v p `orE`
    InfixApp p o |$| step v q

-- Case
step _ (Case _ []) = error "Case with no branches?"
step v (Case e alts@(Alt l p a bs@(BDecls ds) : as)) =
  case patternMatch v p e of
    Matched rs -> case a of
      UnGuardedAlt x -> yield . applyMatches rs $ mkLet ds x
      -- here we apply the matches over all the guard bodies, which may not
      -- always have the most intuitive results
      GuardedAlts (GuardedAlt m ss x : gs) -> case ss of
        [] -> error "GuardedAlt with no body?"
        [Qualifier (Con (UnQual (Ident s)))]
          | s == "True" -> yield . applyMatches rs $ mkLet ds x
          | s == "False" -> if null gs
            -- no more guards, drop this alt
            then if not (null as) then yield $ Case e as else Failure
            -- drop this guard and move to the next
            else yield $ mkCase (GuardedAlts gs)
          | otherwise -> Failure
        -- Okay this is a bit evil. Basically we pretend the guard is being
        -- evaluated in a let-scope generated from the result of the pattern
        -- match. This allows us to use the same code that is supposed to
        -- implement sharing to work out if the scrutinee needs evaluation.
        -- If it does then we can step the bit that matched specifically
        -- (rather than the whole expression) and then use the laboriously-
        -- (but, with any luck, lazily-) constructed third field of
        -- MatchResult to recreate the rest of the scrutinee around it.
        [Qualifier q] -> case step (matchesToScope rs:ds:v) q of
          Step (Eval q') -> yield . mkCase . newAlt $ q'
          -- pattern matching nested this deeply is bad for readability
          r@(Step (EnvEval
            b@(PatBind _ (PVar n) _ (UnGuardedRhs e) (BDecls [])))) ->
            case mlookup n rs of
              Nothing -> case updateBind b ds of
                Nothing -> r
                Just ds' -> yield $ Case e (Alt l p a (BDecls ds') : as)
              Just (MatchResult _ _ r) -> yield $ Case (r e) alts
          r -> r
        a -> todo "step Case GuardedAlts" a
       where
        newAlt q = GuardedAlts (GuardedAlt m [Qualifier q] x : gs)
        mkCase a = Case e (Alt l p a bs : as)
      GuardedAlts [] -> error "Case branch with no expression?"
    MatchEval e -> case e of
      Eval e' -> yield $ Case e' alts
      r -> Step r
    NoMatch
      | null as -> Failure
      | otherwise -> yield $ Case e as
step _ e@(Case _ _) = todo "step Case" e

-- Let
step _ (Let (BDecls []) e) = yield e
step v (Let (BDecls bs) e) = case step (bs : v) e of
  Step (Eval e') -> yield $ mkLet bs e'
  Step (EnvEval e') -> Step $ tryUpdateBind e' e bs
  r -> r

-- If
step _ (If (Con (UnQual (Ident i))) t f) = case i of
  "True" -> yield t
  "False" -> yield f
  _ -> Failure
step v (If e t f) = (\e -> If e t f) |$| step v e

-- Desugarings
step _ (Do []) = error "Empty do?"
step _ (Do [Qualifier e]) = yield e
step _ (Do [_]) = Failure
step _ (Do (s:ss)) = case s of
  Qualifier e -> yield $ InfixApp e (op ">>") (Do ss)
  Generator s p e -> yield $ InfixApp e (op ">>=")
    (Lambda s [p] (Do ss))
  LetStmt bs -> yield $ Let bs (Do ss)
  s -> todo "step Do" s
 where
  op = QVarOp . UnQual . Symbol

-- Trivialities
step v (Paren p) = step v p
step v (Tuple xs) = case xs of
  [] -> error "Empty tuple?"
  [_] -> error "Singleton tuple?"
  es -> liststep v Tuple es

-- Base cases
step _ (LeftSection _ _) = Done
step _ (RightSection _ _) = Done
step _ (TupleSection _) = Done
step _ (Lit _) = Done
step _ (List []) = Done
step _ (Con _) = Done
step _ (Lambda _ _ _) = Done
step _ e = todo "step _" e

-- | Apply the function to the argument as neatly as possible - i.e. infix
-- or make a section if the function's an operator
app :: Exp -> Exp -> Exp
app (Con q) x | isOperator q = LeftSection x (QConOp q)
app (Var q) x | isOperator q = LeftSection x (QVarOp q)
app (LeftSection x op) y = InfixApp x op y
app (RightSection op y) x = InfixApp x op y
app (TupleSection es) x = go es id
 where
  go (Nothing : es) f = case sequence es of
    Just es' -> Tuple $ f (x : es')
    Nothing -> TupleSection $ map Just (f [x]) ++ es
  go (Just e : es) f = go es (f . (e :))
  go [] _ = error "app TupleSection: full section"
app (Con (Special (TupleCon b i))) x
  | i <= 1 = error "app TupleCon: i <= 0"
  | b /= Boxed = todo "app TupleCon" b
  | otherwise = TupleSection (Just x : replicate (i - 1) Nothing)
app f x = App f x

-- | 'True' if the name refers to a non-tuple operator. Tuples are excluded
-- because they're "mixfix" and therefore need to be considered separately
-- anyway.
isOperator :: QName -> Bool
isOperator (Special Cons) = True
isOperator (UnQual (Symbol _)) = True
isOperator (Qual _ (Symbol _)) = True
isOperator _ = False

-- | Given a list of expressions, evaluate the first one that isn't already
-- evaluated and then recombine them with the given function.
liststep :: Env -> ([Exp] -> Exp) -> [Exp] -> EvalStep
liststep v f es = go es id
 where
  go es g = case es of
    [] -> Done
    e:es -> case step v e of
      Step (Eval e') -> yield . f . g $ e':es
      Done -> go es (g . (e:))
      r -> r

-- | Make a let-expression from a list of bindings and an expression. The
-- list of bindings has unused members removed; if this results in an empty
-- list, the expression is returned unaltered.
mkLet :: Scope -> Exp -> Exp
mkLet ds x = case tidyBinds x ds of
  [] -> x
  ds' -> Let (BDecls ds') x

-- | Create a list of 'Decl' that bind the patterns of the 'MatchResult's
-- to their corresponding expressions.
matchesToScope :: [MatchResult] -> Scope
matchesToScope = map $ \(MatchResult n e _) ->
  PatBind nowhere (PVar n) Nothing (UnGuardedRhs e) (BDecls [])

-- this shouldn't really exist
nowhere :: SrcLoc
nowhere = undefined
-- nowhere = SrcLoc "<nowhere>" 0 0 -- for when Show needs to not choke

-- This code isn't very nice, largely because I anticipate it all being
-- replaced eventually anyway.
-- | Implements primitives like addition and comparison.
magic :: Env -> Exp -> EvalStep
magic v e = case e of
  App (App (Var p) x) y -> rhs (fromQName p) x y
  InfixApp x (QVarOp o) y -> rhs (fromQName o) x y
  _ -> Done
 where
  rhs p x y = case lookup p primitives of
    Just (+*) -> case (step v x, step v y) of
      (Done, Done) -> x +* y
      (Done, y') -> InfixApp x op |$| y'
      (x', _) -> (\e -> InfixApp e op y) |$| x'
     where
      op = QVarOp (UnQual p)
    Nothing -> Done
  lit x = case properFraction (toRational x) of
    (i, 0) -> Lit (Int i)
    (i, r) -> Lit (Frac (toRational i + r))
  con = Con . UnQual . Ident
  unlit (Lit (Int i)) = Just $ toRational i
  unlit (Lit (Frac r)) = Just r
  unlit _ = Nothing
  primitives = map (first Symbol) ops ++
    map (first Ident) funs
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
  funs = [
    ("div", mkOp (Lit . Int . floor) (/))]
  num op = mkOp lit op
  bool op = mkOp (con . show) op
  mkOp f g m n = maybe Done (yield . f) $ g <$> unlit m <*> unlit n

-- | Given an expression and a list of bindings, filter out bindings that
-- aren't used in the expression.
tidyBinds :: Exp -> Scope -> Scope
tidyBinds e v = filter (`elem` keep) v
 where
  keep = go (usedIn e) v
  go p ds = case partition p ds of
    ([], _) -> []
    (ys, xs) -> ys ++ go ((||) <$> p <*> usedIn ys) xs
  binds (PatBind _ (PVar n) _ _ _) = [n]
  binds (FunBind ms) = [funName ms]
  -- FIXME: an InfixDecl can specify multiple ops, and we keep all or
  -- none - should drop the ones we no longer need
  binds (InfixDecl _ _ _ os) = map unOp os
  binds l = todo "tidyBinds binds" l
  usedIn es d = any (\n -> isFreeIn n es) (binds d)
  unOp (VarOp n) = n
  unOp (ConOp n) = n

-- | Continuing evaluation requires the value of the given name from the
-- environment, so try to look it up and step it or substitute it.
need :: Env -> Name -> EvalStep
need v n = case envBreak ((Just n ==) . declName) v of
  (_, _, [], _) -> Done
  (as, bs, c : cs, ds) -> case c of
    PatBind s (PVar n) t (UnGuardedRhs e) (BDecls []) ->
      case step ((bs ++ cs) : ds) e of
        Done -> case mapMaybe (envLookup as) $ freeNames e of
          [] -> yield e
          xs -> todo "panic" xs
        Step (Eval e') -> Step . EnvEval $
          PatBind s (PVar n) t (UnGuardedRhs e') (BDecls [])
        f -> f
    FunBind _ -> Done
    b -> todo "need case" b

-- | Name bound by the equations. Error if not all the matches are for the
-- same function.
funName :: [Match] -> Name
funName [] = error "No matches?"
funName (Match _ n _ _ _ _ : ms) = foldr match n ms
 where
  match (Match _ m _ _ _ _) n | m == n = n
  match m n = error $ "Match names don't? " ++ show (m, n)

-- | Counts the number of patterns on the LHS of function equations.
-- Error if the patterns have different numbers of arguments
funArity :: [Match] -> Int
funArity [] = error "No matches?"
funArity (Match _ n ps _ _ _ : ms) = foldr match (length ps) ms
 where
  match (Match _ _ ps _ _ _) l | length ps == l = l
  match _ _ = error $ "Matches of different arity? " ++ show n

{- Doubtful if this is useful, but I'm keeping it anyway
funToCase :: [Match] -> Exp
funToCase [] = error "No matches?"
-- unsure of whether this is the right SrcLoc
funToCase [Match s _ ps _ (UnGuardedRhs e) (BDecls [])] = Lambda s ps e
funToCase ms@(Match s _ ps _ _ _ : _) = Lambda s qs $ Case e as
 where
  qs = map (PVar . Ident) names
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
-}

-- | Given a pattern binding, an expression, and a scope, try to update the
-- scope with the binding (cf. 'updateBind') - if succesful construct an
-- updated let-expression, otherwise produce an EnvEval with the binding.
tryUpdateBind :: Decl -> Exp -> Scope -> Eval
tryUpdateBind e' e = maybe (EnvEval e') (Eval . flip mkLet e) . updateBind e'

-- | Given a pattern binding, replace one of the same name in the given
-- scope, or 'Nothing' if it wasn't there.
updateBind :: Decl -> Scope -> Maybe Scope
updateBind p@(PatBind _ (PVar n) _ _ _) v = case break match v of
  (_, []) -> Nothing
  (h, _ : t) -> Just $ h ++ p : t
 where
  match (PatBind _ (PVar m) _ _ _) = n == m
  match (FunBind _) = False
  match (InfixDecl _ _ _ _) = False
  match d = todo "updateBind match" d
updateBind l _ = todo "updateBind" l

-- | Find a declaration in the environment by matching on its 'declName'.
envLookup :: Env -> Name -> Maybe Decl
envLookup v n = case envBreak ((Just n ==) . declName) v of
  (_, _, [], _) -> Nothing
  (_, _, c : _, _) -> Just c

-- | If the decl binds a pattern or function, return its name.
declName :: Decl -> Maybe Name
declName (PatBind _ (PVar m) _ _ _) = Just m
declName (FunBind ms) = Just (funName ms)
declName (InfixDecl _ _ _ _) = Nothing
declName d = todo "declName" d

-- | Given a list of lists, find the first item matching the predicate and
-- return
-- (lists with no match, takeWhile p list, dropWhile p list, lists remaining)
envBreak :: (a -> Bool) -> [[a]] -> ([[a]], [a], [a], [[a]])
envBreak _ [] = ([], [], [], [])
envBreak p (x:xs) = case break p x of
  (_, []) -> (x:as, bs, cs, ds)
  (ys, zs) -> ([], ys, zs, xs)
 where
  (as, bs, cs, ds) = envBreak p xs

-- | Assume the name is unqualified, and fetch the name in that case.
-- Error otherwise.
fromQName :: QName -> Name
fromQName (UnQual n) = n
fromQName q = error $ "fromQName: " ++ show q

-- | Given a list of 'MatchResult', substitute the bindings wherever they
-- are not shadowed.
applyMatches :: Data a => [MatchResult] -> a -> a
-- If it's not an Exp, just recurse into it, otherwise try to substitute...
applyMatches ms x = recurse `extT` replaceOne $ x
 where
  replaceOne e@(Var (UnQual m)) = maybe e mrExp $ mlookup m ms
  replaceOne (InfixApp x o@(QVarOp (UnQual m)) y) =
    fromMaybe (InfixApp rx o ry) (mkApp . mrExp <$> mlookup m ms)
   where
    (rx, ry) = (replaceOne x, replaceOne y)
    mkApp f = app (app f rx) ry
  -- ...or else recurse anyway
  replaceOne e = recurse e
  recurse e = gmapT (applyMatches (notShadowed e)) e
  -- Parameter here might be redundant - it's only called on x anyway
  notShadowed e = filter (not . flip shadows e . mrName) ms

-- | Find a 'MatchResult' by name.
mlookup :: Name -> [MatchResult] -> Maybe MatchResult
mlookup m = foldr (\x r -> x <$ guard (m == mrName x) <|> r) Nothing

-- | Produce a 'GenericT' that renames all instances of the given 'Name' to
-- something else that isn't any of the given @['Name']@. Does not apply the
-- rename where the name is shadowed.
alpha :: Data a => Name -> [Name] -> a -> a
alpha n avoid = everywhereBut (shadows n) (mkT $ replaceOne n m)
 where
  -- genNames produces an infinite list, so find cannot give Nothing
  Just m = find (`notElem` avoid) $ case n of
    Ident i -> map Ident $ genNames i ['0' .. '9'] 1
    Symbol s -> map Symbol $ genNames s "!?*#+&$%@." 1
  genNames n xs i = map (n ++) (replicateM i xs) ++ genNames n xs (succ i)
  replaceOne n m r | n == r = m | otherwise = r

-- | Returns 'True' if the 'Name' appears without a corresponding binding
-- anywhere in the structure.
-- Always returns 'True' for @>>=@ and @>>@ if there are any do-expressions
-- present.
isFreeIn :: Data a => Name -> a -> Bool
isFreeIn n x = not (shadows n x) && (is n x || or (gmapQ (isFreeIn n) x))
 where
  is n@(Symbol s)
    | s == ">>" || s == ">>=" = mkQ False (== n) `extQ` isDo
  is n = mkQ False (== n)
  isDo (Do _) = True
  isDo _ = False

-- | Fetches a list of all 'Name's present but not bound in the argument.
freeNames :: Data a => a -> [Name]
freeNames e = filter (`isFreeIn` e) . Set.toList . Set.fromList $
  listify (const True) e

-- | If the argument is 'Step', turn it into a 'MatchEval', else 'NoMatch'.
peval :: EvalStep -> PatternMatch
peval (Step e) = MatchEval e
peval _ = NoMatch

-- | Match a single pattern against a single expression.
patternMatch :: Env -> Pat -> Exp -> PatternMatch
-- Strip parentheses
patternMatch v (PParen p) x = patternMatch v p x
patternMatch v p (Paren x) = patternMatch v p x
-- Patterns that always match
patternMatch _ (PWildCard) _ = Matched []
patternMatch _ (PVar n) x = Matched [MatchResult n x id]
-- As-patterns
patternMatch v (PAsPat n p) x = case patternMatch v p x of
  Matched ms -> Matched (MatchResult n x id : ms)
  r -> r
-- Let-expressions should skip right to the interesting bit
patternMatch v p (Let (BDecls ds) x) = case patternMatch (ds:v) p x of
  MatchEval (Eval e) -> MatchEval . Eval $ mkLet ds e
  MatchEval (EnvEval e) -> MatchEval $ tryUpdateBind e x ds
  r -> r
patternMatch _ _ (Let bs _) = todo "patternMatch Let" bs
-- Variables can only match trivial patterns
patternMatch v p (Var q) = case envBreak ((Just n ==) . declName) v of
  (_, _, [], _) -> NoMatch
  (_, xs, y : ys, zs) -> case y of
    PatBind s q t (UnGuardedRhs e) bs -> case patternMatch v' p e of
      MatchEval (Eval e') ->
        MatchEval (EnvEval (PatBind s q t (UnGuardedRhs e') bs))
      Matched _ -> MatchEval (Eval e)
      r -> r
     where
      v' = (xs ++ ys) : zs
    FunBind _ -> NoMatch
    l -> todo "patternMatch Var" l
 where
  n = fromQName q
-- Desugar infix applications and lists
patternMatch v (PInfixApp p q r) s = patternMatch v (PApp q [p, r]) s
patternMatch v p e@(InfixApp a n b) = case n of
  QVarOp _ -> peval $ step v e
  QConOp q -> patternMatch v p (App (App (Con q) a) b)
patternMatch _ _ (List (x:xs)) = MatchEval . Eval $
  InfixApp x (QConOp (Special Cons)) (List xs)
patternMatch _ _ (Lit (String (x:xs))) = MatchEval . Eval $
  InfixApp (Lit (Char x)) (QConOp (Special Cons)) (Lit (String xs))
-- Literal match
patternMatch _ (PLit p) (Lit q)
  | p == q = Matched []
  | otherwise = NoMatch
patternMatch v (PLit _) s = peval $ step v s
patternMatch v (PList []) x = case argList x of
  [List []] -> Matched []
  [List _] -> NoMatch
  Con _ : _ -> NoMatch
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
    | c == n -> matches v ps xs (unArgList (Con c))
    | otherwise -> NoMatch
  _ -> peval $ step v q
-- Fallback case
patternMatch _ p q = todo "patternMatch _" (p, q)

-- | Map over the function field of a 'MatchResult'.
onMRFunc :: ((Exp -> Exp) -> (Exp -> Exp)) -> MatchResult -> MatchResult
onMRFunc f m@(MatchResult { mrFunc = g }) = m { mrFunc = f g }

-- The tricky part about this is the third field of PatternMatch, which
-- contains a function to put the matchresult - perhaps after some
-- modification - back into its original context.
-- This is something that is mostly best understood by example. Luckily I've
-- provided an evil Show instance for Exp -> Exp so you should be able to
-- see its purpose in a bit of mucking about with ghci :)
-- Obviously it starts off as id.
-- | Carry out several simultaneous pattern matches, e.g. for lists or
-- tuples of patterns. The given function is used to restore the list of
-- expressions to their original context if necessary (so it might be the
-- Tuple constructor, for example).
matches :: Env -> [Pat] -> [Exp] -> ([Exp] -> Exp) -> PatternMatch
matches _ [] [] _ = Matched []
matches v ps xs f = go v ps xs id
 where
  go _ [] [] _ = Matched []
  go v (p:ps) (e:es) g =
    -- We rely on laziness here to not recurse if the first match fails.
    -- If we do recurse, then the reconstruction function needs to
    -- put the current expression on the end.
    case (patternMatch v p e, go v ps es (g . (e:))) of
      (NoMatch, _) -> NoMatch
      (MatchEval (Eval e'), _) -> MatchEval . Eval . f . g $ e' : es
      (r@(MatchEval _), _) -> r
      (Matched xs, Matched ys) ->
        -- great, everything worked fine. Now we assume the recursive case
        -- has everything worked out and we just need to apply the final
        -- touches to the reconstruction function.
        -- So far it'll be a [Exp] -> [Exp] that basically consists of
        -- everything we've skipped to get this far in the pattern match.
        -- We want to also append everything we haven't met yet (making
        -- an Exp -> [Exp]) and then apply the combination function given
        -- as a parameter (making Exp -> Exp, which is what we need). We
        -- do this for every pattern match item.
        Matched (map (onMRFunc ((f . g . (: es)) .)) xs ++ ys)
      (_, r) -> r
      -- Ran out of patterns before expressions or vice versa, fail
      -- TODO: matches should get a [(Pat, Exp)] so the equality of length
      -- is statically enforced.
  go _ _ _ _ = NoMatch

-- | Deconstruct an infix or prefix application into
-- @[function, arg1, arg2, ...]@. Spine-strict by the nature of application.
argList :: Exp -> [Exp]
argList = reverse . atl
 where
  atl (App f x) = x : atl f
  atl (Paren p) = atl p
  atl (InfixApp p o q) = [q, p, case o of
    QVarOp n -> Var n
    QConOp n -> Con n]
  atl e = [e]

-- This could be optimised because app checks for atomic functions but we
-- know after the first app that none of the subsequent functions are so.
-- | @'foldl' 'app'@. Apply a function to a list of arguments, neatly.
unArgList :: Exp -> [Exp] -> Exp
unArgList = foldl app

-- | Return 'True' if the argument binds the given 'Name'
shadows :: Typeable a => Name -> a -> Bool
shadows n = mkQ False exprS `extQ` altS `extQ` matchS
 where
  exprS (Lambda _ ps _) = any patS ps
  exprS (Let (BDecls bs) _) = any letS bs
  exprS _ = False
  altS (Alt _ p _ (BDecls bs)) = patS p || any letS bs
  altS a = todo "shadows altS" a
  matchS (Match _ _ ps _ _ _) = any patS ps
  patS (PVar m) = m == n
  patS (PAsPat m p) = m == n || patS p
  patS p = or $ gmapQ (mkQ False patS) p
  letS (PatBind _ p _ _ _) = patS p
  letS _ = False

-- | 'True' if the predicate holds anywhere inside the structure.
anywhere :: (Typeable a, Data b) => (a -> Bool) -> b -> Bool
anywhere p = everything (||) (mkQ False p)

todo :: (Show s) => String -> s -> a
todo s = error . (s ++) . (": Not implemented: " ++) . show

