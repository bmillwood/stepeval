module Parenthise (enparen, deparen) where

import Data.Generics (everywhere, mkT)
import Language.Haskell.Exts

deparen :: Exp -> Exp
deparen = everywhere (mkT dp)
 where dp (Paren p) = dp p
       dp r = r

enparen :: Exp -> Exp
enparen = enparenWithFixities preludeFixities

enparenWithFixities :: [Fixity] -> Exp -> Exp
enparenWithFixities fixes = everywhere (mkT reparen) . deparen
 where reparen (App f x) = App (parenIf fp f) (parenIf xp x)
        where parenIf p x
               | p x = Paren x
               | otherwise = x
              fp (Lambda _ _ _) = True
              fp _ = False
              xp (Lambda _ _ _) = True
              xp (InfixApp _ _ _) = True
              xp _ = False
       reparen e@(InfixApp l p r@(InfixApp _ q _))
        | qf > pf = e
        | qf == pf && qa == AssocRight && pa == AssocRight = e
        | otherwise = InfixApp l p (Paren r)
        where Fixity qa qf _ = qFix q
              Fixity pa pf _ = qFix p
       reparen e@(InfixApp l@(InfixApp _ q _) p r)
        | qf > pf = e
        | qf == pf && qa == AssocLeft && pa == AssocLeft = e
        | otherwise = InfixApp (Paren l) p r
        where Fixity qa qf _ = qFix q
              Fixity pa pf _ = qFix p
       reparen e = e
       unQOp (QVarOp (UnQual q)) = VarOp q
       unQOp (QConOp (UnQual q)) = ConOp q
       unQOp (QConOp (Special Cons)) = ConOp (Symbol ":")
       unQOp q = error $ "unQOp: " ++ show q
       qFix = getFix . unQOp
       getFix o = foldr
        (\f@(Fixity _ _ p) r -> if o == p then f else r)
        (Fixity AssocLeft 9 o) fixes

-- this is entirely silly
instance Num Exp where
 x + y = InfixApp x (QVarOp (UnQual (Symbol "+"))) y
 x * y = InfixApp x (QVarOp (UnQual (Symbol "*"))) y
 abs x = App (Var (UnQual (Ident "abs"))) x
 signum x = App (Var (UnQual (Ident "signum"))) x
 fromInteger = Lit . Int

