module Parenthise (deparen, enparen, enparenWith, scopeToFixities) where

import Data.Generics (GenericT, everywhere, extT, gmapT, mkT)
import Data.Foldable (foldMap)
import Data.Monoid (Any (Any, getAny))
import Language.Haskell.Exts

scopeToFixities :: [Decl] -> [Fixity]
scopeToFixities = concatMap dToF
 where
  dToF (InfixDecl _ a i os) = map (Fixity a i . UnQual . unOp) os
  dToF _ = []
  unOp (VarOp n) = n
  unOp (ConOp n) = n

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
 where
  app ps x = parenIf (anyP ps) $ parenE xs x
  fp = [isLet, isLambda, isIApp]
  xp = [isLet, isLambda, isIApp, isApp]

parenE xs (InfixApp l p r)
  | anyP [isLet, isLambda] l = parenE xs $ InfixApp (Paren l) p r

parenE xs (InfixApp l p r@(InfixApp _ q _))
 | qf > pf = recurse
 | qf == pf && qa == AssocRight && pa == AssocRight = recurse
 | otherwise = InfixApp l' p (Paren r')
 where Fixity qa qf _ = qFix xs q
       Fixity pa pf _ = qFix xs p
       (l', r') = (parenE xs l, parenE xs r)
       recurse = InfixApp l' p r'

parenE xs (InfixApp l@(InfixApp _ q lr) p r)
 | isLet lr || isLambda lr = InfixApp (Paren l') p r'
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

parenIf :: (Exp -> Bool) -> Exp -> Exp
parenIf = appIf Paren

appIf :: (a -> a) -> (a -> Bool) -> a -> a
appIf f p x
 | p x = f x
 | otherwise = x

qFix :: [Fixity] -> QOp -> Fixity
qFix xs (QVarOp q) = getFix xs q
qFix xs (QConOp (Special Cons)) = getFix xs (UnQual (Symbol ":"))
qFix xs (QConOp q) = getFix xs q

getFix :: [Fixity] -> QName -> Fixity
getFix xs o = foldr
 (\f@(Fixity _ _ p) r -> if o == p then f else r)
 (Fixity AssocLeft 9 o) xs

isLambda, isIApp, isApp :: Exp -> Bool
isLambda (Lambda {}) = True
isLambda _ = False
isLet (Let {}) = True
isLet _ = False
isIApp (InfixApp {}) = True
isIApp _ = False
isApp (App {}) = True
isApp _ = False

anyP :: [a -> Bool] -> a -> Bool
anyP = result getAny . foldMap (result Any)

result :: (r -> r') -> (a -> r) -> (a -> r')
result = (.)

