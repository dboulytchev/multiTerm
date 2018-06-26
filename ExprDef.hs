{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE FlexibleContexts           #-}

module ExprDef where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm
import Data.List ((\\), nub, concat, delete)
import Data.Maybe
import Cas

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving (Show, Eq)
data Def  = Def String Expr deriving (Show, Eq)

instance Term Expr where
  type Var Expr = String
  type Sub Expr = Expr :|: Def :|: U

  subterms (Var   _)   = Nil
  subterms (Const _)   = Nil
  subterms (Bop _ l r) = Cons l (Cons r Nil)
  subterms (Let d e)   = Cons d (Cons e Nil)

  var (Var x) = Just x
  var _ = Nothing

  binder (Let (Def a _) _) = Just a
  binder _                 = Nothing

  make (Bop b _ _) subs = let ([l', r'] :+: [] :+: _) = reify subs in Bop b l' r'
  make (Let _ _  ) subs = let ([e'] :+: [d'] :+: _)  = reify subs in Let d' e'
  make t           _    = t

instance Term Def where
  type Var Def = String
  type Sub Def = Expr :|: Def :|: U

  subterms (Def _ e) = Cons e Nil

  var _ = Nothing

  binder (Def s _) = Just s

  make (Def s _) subs = let ([e'] :+: [] :+: _) = reify subs in Def s e'

flipBop = rewrite $ (\expr -> case expr of Bop b l r -> Bop b r l ; e -> e) :+: id :+: undefined

simplBop = rewrite (simpl :+: id :+: undefined)
  where simpl (Bop "+" (Const 0) r) = r
        simpl (Bop "+" l (Const 0)) = l
        simpl (Bop "*" (Const 1) r) = r
        simpl (Bop "*" l (Const 1)) = l
        simpl e                     = e

instance FreeVars Def
instance FreeVars Expr


instance CAS Def where
  rename (Def _ b)   x = Def x b

  freshVar vs = let v = head $ names \\ vs in (v, undefined)
    where names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']

instance CAS Expr where
  rename (Var _)   x = Var x
  rename y         _ = y

  freshVar vs = let v = head $ names \\ vs in (v, Var v)
    where names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']

sb expr = sb' expr (simplBop expr)
  where sb' prev curr | prev == curr = curr
        sb' _    curr = sb' curr (simplBop curr)

fv :: Expr -> [Var Expr]
fv e = fold (shallowFv :+: shallowFv :+: undefined) e []

foldish e = fold ((\e a -> case e of Var x -> x : a ; _ -> a) :+: (\ d a -> case d of Def x _ -> x `delete` a ) :+: undefined) e []

foldtest e = fold ((\e (e', a) -> case var e of Just v -> (Var (v ++ v), v:a); _ -> (e',a)) :+: (\d (d', a) -> (d', a)) :+: undefined) e (e, [] :: [String])

equalStruct (Bop b l r, Bop b' l' r') | b == b' = equalStruct (l, l') && equalStruct (r, r')
equalStruct (Const _, Const _) = True
equalStruct (Var _, Var _) = True
equalStruct (Let d e, Let d' e') = equalStructD (d, d') && equalStruct (e, e')
equalStruct _ = False

equalStructD (Def _ e, Def _ e') = equalStruct (e, e')

eqStruct (Bop b _ _, Bop b' _ _) | b == b' = True
eqStruct (Const _, Const _) = True
eqStruct (Var _, Var _) = True
eqStruct (Let _ _, Let _ _) = True
eqStruct _ = False

eqStructD _ _ = True


t  = Bop "+" (Var "a")  (Let (Def "b" (Bop "+" (Bop "*" (Const 1) (Const 7)) (Const 0))) (Bop "+" (Const 6) (Var "b")))
t1 = Bop "+" (Var "x")  (Let (Def "y" (Bop "+" (Bop "*" (Const 13) (Const 42)) (Const 0))) (Bop "+" (Const 666) (Var "b")))
t2 = Bop "+" (Var "x")  (Let (Def "y" (Bop "+" (Bop "*" (Const 13) (Const 42)) (Const 0))) (Bop "*" (Const 666) (Var "b")))
t3 = Let (Def "y" (Bop "+" (Bop "*" (Const 13) (Const 42)) (Const 0))) (Bop "+" (Const 666) (Var "b"))

runTest f = do
  print f
  putStrLn ""

test :: IO ()
test =
  do
    runTest t
    runTest $ foldtest t
    runTest $ flipBop t
    runTest $ simplBop t
    runTest $ sb t
    runTest $ foldish t
    runTest $ fv t
    runTest $ freeVars t
    runTest $ equalStruct (t, t1)
    runTest $ equalStruct (t, t2)
    runTest $ equalStruct (t, t3)
    runTest $ equalStruct (t2, t)
