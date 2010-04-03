module Parenthise (deparen, enparen, enparenWith, scopeToFixities) where

import Data.Generics (GenericT, everywhere, extT, gmapT, mkT)
import Language.Haskell.Exts

scopeToFixities :: [Decl] -> [Fixity]
scopeToFixities = concatMap dToF
 where dToF (InfixDecl _ a i os) = map (Fixity a i) os
       dToF _ = []

deparen :: Exp -> Exp
deparen = everywhere (mkT dp)
 where dp (Paren p) = dp p
       dp r = r

enparen :: GenericT
enparen = enparenWith []

enparenWith :: [Fixity] -> GenericT
enparenWith xs = recurse
 where recurse :: GenericT
       recurse = gmapT recurse `extT` parenE xs `extT` parenM xs

parenE :: [Fixity] -> Exp -> Exp
parenE xs (Let (BDecls bs) e) = Let (BDecls bs') e'
 where xs' = scopeToFixities bs ++ xs
       bs' = enparenWith xs' bs
       e' = parenE xs' e

parenE xs (App f x) = App (app fp f) (app xp x)
 where app p x = appIf Paren p $ parenE xs x
       fp x = isLambda x || isIApp x
       xp x = isLambda x || isIApp x || isApp x

parenE xs (InfixApp l p r@(InfixApp _ q _))
 | qf > pf = recurse
 | qf == pf && qa == AssocRight && pa == AssocRight = recurse
 | otherwise = InfixApp l' p (Paren r')
 where Fixity qa qf _ = qFix xs q
       Fixity pa pf _ = qFix xs p
       (l', r') = (parenE xs l, parenE xs r)
       recurse = InfixApp l' p r'

parenE xs (InfixApp l@(InfixApp _ q _) p r)
 | qf > pf = recurse
 | qf == pf && qa == AssocLeft && pa == AssocLeft = recurse
 | otherwise = InfixApp (Paren l') p r'
 where Fixity qa qf _ = qFix xs q
       Fixity pa pf _ = qFix xs p
       (l', r') = (parenE xs l, parenE xs r)
       recurse = InfixApp l' p r'

parenE xs e = gmapT (enparenWith xs) e

parenM :: [Fixity] -> Match -> Match
parenM xs (Match s n ps t r bs) = Match s n (f ps) t (f r) (f bs)
 where f :: GenericT
       f = enparenWith $ case bs of
        BDecls ds -> scopeToFixities ds ++ xs
        _ -> xs

appIf :: (a -> a) -> (a -> Bool) -> a -> a
appIf f p x
 | p x = f x
 | otherwise = x

qFix :: [Fixity] -> QOp -> Fixity
qFix xs (QVarOp (UnQual q)) = getFix xs (VarOp q)
qFix xs (QConOp (UnQual q)) = getFix xs (ConOp q)
qFix xs (QConOp (Special Cons)) = getFix xs (ConOp (Symbol ":"))
qFix _ q = error $ "qFix: " ++ show q

getFix :: [Fixity] -> Op -> Fixity
getFix xs o = foldr
 (\f@(Fixity _ _ p) r -> if o == p then f else r)
 (Fixity AssocLeft 9 o) xs

isLambda, isIApp, isApp :: Exp -> Bool
isLambda (Lambda _ _ _) = True
isLambda _ = False
isIApp (InfixApp _ _ _) = True
isIApp _ = False
isApp (App _ _) = True
isApp _ = False

-- this is entirely silly
instance Num Exp where
 x + y = InfixApp x (QVarOp (UnQual (Symbol "+"))) y
 x * y = InfixApp x (QVarOp (UnQual (Symbol "*"))) y
 abs x = App (Var (UnQual (Ident "abs"))) x
 signum x = App (Var (UnQual (Ident "signum"))) x
 fromInteger = Lit . Int

