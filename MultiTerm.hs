{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module MultiTerm where

import Prelude hiding (foldl)
import HeteroList
import Data.List ((\\), nub, concat, delete)
import Data.Maybe

data Direction = BottomUp | TopDown

class Term t where
  type Var t :: *
  type Sub t :: *

  var       :: t -> Maybe (Var t)
  binder    :: t -> Maybe (Var t)
  subterms  :: t -> HeteroList (Sub t)
  make      :: t -> HeteroList (Sub t) -> t

class Term t => FreeVars t where
  shallowFv :: (Eq (Var t)) => t -> [Var t] -> [Var t]
  shallowFv t a = case var t of
                    Just  v -> v : a
                    Nothing -> case binder t of
                                 Just v  -> filter (/= v) a
                                 Nothing -> a

  freeVars :: ( Eq (Var t),
                MakeFv (Sub t) (Var t),
                LiftFold (Sub t) (Sub t) [Var t],
                MakeFolder (Sub t) (Sub t) [Var t],
                ApplyUniform (Sub t) t
              ) => t -> [Var t]
  freeVars e = nub $ fold TopDown makeFv e []


type family ShallowRewriter t g = r | r -> t g where
  ShallowRewriter t g = Transform g -> Transform g -> t -> t

class Term t => ShallowRewrite t where
  shallowRewrite :: Direction -> ShallowRewriter t (Sub t)

instance (ApplyTransform (Sub t) t, Term t) => ShallowRewrite t where
  shallowRewrite direction deep shallow t =
    case direction of
      BottomUp -> let t' = make t (mapTransform deep (subterms t)) in
                  applyTransform shallow t'
      TopDown  -> let  t' = applyTransform shallow t in
                  make t' $ mapTransform deep (subterms t')

type family LiftRewriter t g = r | r -> t g where
  LiftRewriter (a :|: b) g = ShallowRewriter a g :+: LiftRewriter b g

class LiftRewrite t g where
  liftRewrite :: Direction -> LiftRewriter t g

instance (Term a, g ~ Sub a, ApplyTransform (Sub a) a, LiftRewrite b g) => LiftRewrite (a :|: b) g where
  liftRewrite d = shallowRewrite d :+: liftRewrite d

instance LiftRewrite U g where
  liftRewrite _ = undefined

class MakeRewriter t g where
  makeRewriter :: LiftRewriter t g -> Transform g -> Transform g -> Transform t

instance MakeRewriter U g where
  makeRewriter _ _ _ = undefined

instance (Term t, MakeRewriter q g) => MakeRewriter (t :|: q) g where
  makeRewriter ((t :: ShallowRewriter t g) :+: (q :: LiftRewriter q g)) (a :: Transform g) (b :: Transform g) =
    let f :: t -> t      = t a b              in
    let g :: Transform q = makeRewriter q a b in
    f :+: g

class Term t => Rewrite t where -- t -- phantom parameter
  rewrite :: Direction -> Transform (Sub t) -> t -> t

instance (Term t, LiftRewrite (Sub t) (Sub t), MakeRewriter (Sub t) (Sub t), ApplyTransform (Sub t) t) => Rewrite t where
  rewrite d shallow t =
    let fs = makeRewriter ((liftRewrite d  :: LiftRewriter (Sub t) (Sub t)))
                          (fs :: Transform (Sub t))
                          (shallow :: Transform (Sub t))
    in applyTransform fs t



type family ShallowFolder t g c = r | r -> t g c where
  ShallowFolder t g c = Uniform g (c -> c) -> Uniform g (c -> c) -> t -> c -> c

class Term t => ShallowFold t c where
  shallowFold :: Direction -> ShallowFolder t (Sub t) c

instance (Term t, ApplyUniform (Sub t) t) => ShallowFold t c where
  shallowFold d deep shallow t acc =
    case d of
      BottomUp -> polyfoldl deep (subterms t) (applyUniform shallow t acc)
      TopDown  -> applyUniform shallow t (polyfoldl deep (subterms t) acc)

class MakeFolder t g c where
  makeFolder  :: LiftFolder t g c -> Uniform g (c -> c) -> Uniform g (c -> c) -> Uniform t (c -> c)

instance MakeFolder U g c where
  makeFolder _ _ _ = undefined

instance (Term a, MakeFolder b g c) => MakeFolder (a :|: b) g c where
  makeFolder (t :+: q) a b =
    let f = t a b in
    let g = makeFolder q a b in
    f :+: g

type family LiftFolder t g c = r | r -> t g c where
  LiftFolder (a :|: b) g c = ShallowFolder a g c :+: LiftFolder b g c

class LiftFold t g c where
  liftFold :: Direction -> LiftFolder t g c

instance LiftFold U g c where
  liftFold _ = undefined

instance (Term a, g ~ Sub a, ApplyUniform g a, LiftFold b g c) => LiftFold (a :|: b) g c where
  liftFold d = shallowFold d :+: liftFold d

class Term t => Fold t c where
  fold :: Direction -> Uniform (Sub t) (c -> c) -> t -> c -> c

instance (Term t, LiftFold (Sub t) (Sub t) c, MakeFolder (Sub t) (Sub t) c, ApplyUniform (Sub t) t) => Fold t c where
  fold d shallow t acc =
    let fs = makeFolder (liftFold d) fs shallow
    in applyUniform fs t acc


class MakeFv u v where
  makeFv :: Uniform u ([v] -> [v])

instance MakeFv U v where
  makeFv = undefined

instance (Term a, FreeVars a, v ~ Var a, Eq v, MakeFv b v) =>  MakeFv (a :|: b) v where
  makeFv = shallowFv :+: makeFv