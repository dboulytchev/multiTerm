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
import Unsafe.Coerce

class Term t where
  type Var t :: *
  type Sub t :: *

  var      :: t -> Maybe (Var t)
  binder   :: t -> Maybe (Var t)
  subterms :: t -> HeteroList (Sub t)
  make     :: t -> HeteroList (Sub t) -> t
  makeFV   :: (Eq (Var t)) => t -> [Var t] -> [Var t]

  makeFV t a = case var t of
                 Just  v -> v : a
                 Nothing -> case binder t of
                              Just v  -> filter (/= v) a
                              Nothing -> a

type family ShallowRewriter t g = r | r -> t g where
  ShallowRewriter t g = Transform g -> Transform g -> t -> t

class Term t => ShallowRewrite t where
  shallowRewrite :: ShallowRewriter t (Sub t)

instance (ApplyTransform (Sub t) t, Term t) => ShallowRewrite t where
  shallowRewrite deep shallow t =
    let  t' = applyTransform shallow t in
    make t' $ mapTransform deep (subterms t')

type family LiftRewriter t g = r | r -> t g where
  LiftRewriter (a :|: b) g = ShallowRewriter a g :+: LiftRewriter b g

class LiftRewrite t g where
  liftRewrite :: LiftRewriter t g

instance (Term a, g ~ Sub a, ApplyTransform (Sub a) a, LiftRewrite b g) => LiftRewrite (a :|: b) g where
  liftRewrite = shallowRewrite :+: liftRewrite

instance LiftRewrite U g where
  liftRewrite = undefined

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
  rewrite :: Transform (Sub t) -> t -> t

instance (Term t, LiftRewrite (Sub t) (Sub t), MakeRewriter (Sub t) (Sub t), ApplyTransform (Sub t) t) => Rewrite t where
  rewrite shallow t =
    let fs = makeRewriter (liftRewrite :: LiftRewriter (Sub t) (Sub t))
                          (fs :: Transform (Sub t))
                          (shallow :: Transform (Sub t))
    in applyTransform fs t