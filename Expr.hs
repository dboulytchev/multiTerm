{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}

import MultiTerm

data Expr = Var String | Const Int | Bop String Expr Expr | D Def Expr deriving Show
data Def  = Def String Expr deriving Show

instance Term Def where
  type Var Def = String
  type Sub Def = [Expr] :+: [Def]
  var _ = Nothing

  binder (Def s _) = Just s

  eq _ _ = True

  subterms (Def _ e) = [e] :+: []

  make (Def s _) ([e] :+: []) = Def s e

instance Term Expr where
  type Var Expr = String
  type Sub Expr =  [Expr] :+: [Def]

  var (Var s) = Just s
  var  _      = Nothing

  binder _    = Nothing

  eq (Var     _) (Var     _) = True
  eq (Const   _) (Const   _) = True
  eq (Bop _ _ _) (Bop _ _ _) = True
  eq (D   _ _  ) (D   _ _  ) = True
  eq  _           _          = False

  subterms (Var _)     = [] :+: []
  subterms (Const _)   = [] :+: []
  subterms (Bop _ l r) = [l, r] :+: []
  subterms (D   d e)   = [e] :+: [d]

  make t@(Var _  )  _               = t
  make t@(Const _)  _               = t
  make (Bop b _ _) ([l, r] :+: [] ) = Bop b l r
  make (D   _ _  ) ([e]    :+: [d]) = D d e

expr = Bop "+" (Var "a") (D (Def "b" (Bop "+" (Const 1) (Const 0))) (Bop "+" (Const 0) (Var "b")))

homhom :: (Expr -> Expr) -> Expr -> Expr
homhom f t = 
  let s  = subterms t in 
  let fs = apply (makeHom (homhom f) :: Distrib (Lift (Sub Expr))) fs in
  f $ make t $ choose s fs

elim0 = hom (\ t -> case t of
                      Bop "+" e (Const 0) -> e
                      Bop "+" (Const 0) e -> e
                      _                   -> t
            )

main = putStrLn $ show $ elim0 expr