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

module Eq where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm

class Term t => Equalushko t where
  equalushko :: t -> t -> Bool

class FlatEq u v where
  flatEq :: Uniform u (Uniform v Bool)

instance FlatEq U v where
  flatEq = undefined

instance (Const v Bool, Equalushko a, Update v a Bool, FlatEq b v) => FlatEq (a :|: b) v where
  flatEq =
    (\t -> update (equalushko t) $ uniConst False) :+: flatEq

class (Term t, FlatEq (Sub t) (Sub t),
       MakeEqualer (Sub t) (Sub t) (Sub t) (Sub t),
       LiftEqual (Sub t) (Sub t) (Sub t),
       ApplyUniform (Sub t) t) => Equal t where
  equal :: t -> t -> Bool
  equal t s =
    let fs = makeEqualer liftEqual fs flatEq in
    applyUniform (applyUniform fs t :: Uniform (Sub t) Bool) s

type family ShallowEqualer t u v = r | r -> t u v where
  ShallowEqualer t u v = Uniform u (Uniform v Bool) -> Uniform u (Uniform v Bool) -> t -> t -> Bool

class ShallowEqual t where
  shallowEqual :: ShallowEqualer t (Sub t) (Sub t)

instance (Show t, ApplyUniform (Sub t) t, Term t) => ShallowEqual t where
  shallowEqual deep shallow t s =
    applyUniform (applyUniform shallow t) s &&
      (
        let t_subs = subterms t in
        let s_subs = subterms s in
        heteroLength t_subs == heteroLength s_subs && (and $ heteroZipWith deep t_subs s_subs)
      )

class MakeEqualer n u v m where
  makeEqualer :: LiftEqualer n u v m -> Uniform u (Uniform v Bool) -> Uniform u (Uniform v Bool) -> Uniform n (Uniform m Bool)

instance MakeEqualer U u v m where
  makeEqualer _ _ _ = undefined

instance (Show a, MakeEqualer b u v m, Update m a Bool, Const m Bool) => MakeEqualer (a :|: b) u v m where
  makeEqualer (p :+: q) a b =
    let f = \t -> update (p a b t) (uniConst False) in
    let g = makeEqualer q a b in
    f :+: g

type family LiftEqualer n u v m = r | r -> n u v m where
  LiftEqualer (a :|: b) u v m = ShallowEqualer a u v :+: LiftEqualer b u v m

class LiftEqual n u m where
  liftEqual :: LiftEqualer n u u m

instance LiftEqual U u m where
  liftEqual = undefined

instance (Term a,
          u ~ Sub a,
          ShallowEqual a,
          LiftEqual b u m) => LiftEqual (a :|: b) u m where
  liftEqual = shallowEqual :+: liftEqual