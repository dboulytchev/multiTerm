{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module MultiTerm where

import Data.Maybe 
import Data.List

class Term t where
  type Var t :: *
  type Sub t :: *

  subterms   :: t -> Sub t
  var        :: t -> Maybe (Var t)
  binder     :: t -> Maybe (Var t)
  eq         :: t -> t -> Bool
  make       :: t -> Sub t -> t

  multiRewriteBottomUp  :: (
                            MakeRewrite BottomUp (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                            Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                            Discriminate (Rewrite (Sub t)) (Sub t), 
                            Subtype t (Sub t), 
                            Term t
                           ) => Rewrite (Sub t) -> t -> t

  multiRewriteTopDown  :: (
                           MakeRewrite TopDown (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                           Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                           Discriminate (Rewrite (Sub t)) (Sub t), 
                           Subtype t (Sub t), 
                           Term t
                          ) => Rewrite (Sub t) -> t -> t

  rewriteBottomUp      :: (
                           LiftRewrite (t -> t) (Rewrite (Sub t)),
                           MakeRewrite BottomUp (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                           Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                           Discriminate (Rewrite (Sub t)) (Sub t), 
                           Subtype t (Sub t), 
                           Term t
                          ) => (t -> t) -> t -> t

  rewriteTopDown       :: (                 
                           LiftRewrite (t -> t) (Rewrite (Sub t)),
                           MakeRewrite TopDown (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                           Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                           Discriminate (Rewrite (Sub t)) (Sub t), 
                           Subtype t (Sub t), 
                           Term t
                          ) => (t -> t) -> t -> t

  multiRewriteBottomUp f t = 
    let fs = apply (makeRewrite BU f :: ShallowRewrite (Sub t)) fs in 
    let t' = make t $ discriminate (subterms t) fs in
    ((prj $ discriminate (inj t' :: Sub t) f) :: t) 

  multiRewriteTopDown f t = 
    let fs = apply (makeRewrite TD f :: ShallowRewrite (Sub t)) fs in 
    let t' = ((prj $ discriminate (inj t :: Sub t) f) :: t) in
    make t' $ discriminate (subterms t') fs

  rewriteBottomUp f t = multiRewriteBottomUp (liftRewrite f) t
  rewriteTopDown  f t = multiRewriteTopDown  (liftRewrite f) t

data BottomUp = BU
data TopDown  = TD

infixr 5 :+:

data h :+: t = h :+: t deriving Show

class Default a where
  value :: a

instance Default [a] where
  value = []

instance (Default a, Default b) => Default (a :+: b) where
  value = value :+: value

class Subtype a b where
  inj :: a -> b
  prj :: b -> a

instance Subtype a [a] where
  inj  a  = [a]
  prj [a] =  a 

instance (Default c, Subtype a b) => Subtype a (c :+: b) where
  inj a         = value :+: inj a
  prj (_ :+: b) = prj b

instance {-# OVERLAPPING #-} Default b => Subtype a ([a] :+: b) where
  inj   a         = [a] :+: value
  prj ([a] :+: _) =  a

type family Dom a where
  Dom (a -> b) = a

type family Cod a where
  Cod (a -> b) = b

type family Rewrite a where
  Rewrite [f]         = f -> f
  Rewrite ([a] :+: b) = (a -> a) :+: Rewrite b

type family Lift a where
  Lift [f]       = (f -> f) -> f -> f
  Lift (a :+: b) = (Dom (Lift a) :+: Dom (Lift b) -> Cod (Lift a) :+: Cod (Lift b))

type family Distrib a where
  Distrib (c -> a :+: b) = (c -> a) :+: (c -> b)
  Distrib (c -> a)       = c -> a

type family ShallowRewrite a where
  ShallowRewrite a = Distrib (Lift a)

class LiftRewrite f fs where
  liftRewrite :: f -> fs

instance LiftRewrite (t -> t) (a -> a) where
  liftRewrite f t = t

instance {-# OVERLAPPING #-} LiftRewrite (t -> t) (t -> t) where
  liftRewrite f x = f x
  
instance (LiftRewrite f fs, LiftRewrite f gs) => LiftRewrite f (fs :+: gs) where
  liftRewrite f = liftRewrite f :+: liftRewrite f

class MakeRewrite dir f fs where
  makeRewrite :: dir -> f -> fs

instance (Discriminate c (Sub t), Term t) => MakeRewrite BottomUp (t -> t) (c -> t -> t) where
  makeRewrite dir f c = \ t -> f $ make t $ discriminate (subterms t) c -- let t' = f t in make t' $ discriminate (subterms t') c

instance (Discriminate c (Sub t), Term t) => MakeRewrite TopDown (t -> t) (c -> t -> t) where
  makeRewrite dir f c = \ t -> let t' = f t in make t' $ discriminate (subterms t') c

instance {-# OVERLAPPING #-} (MakeRewrite d f fs, MakeRewrite d g gs) => MakeRewrite d (f :+: g) (fs :+: gs) where
  makeRewrite dir (f :+: g) = makeRewrite dir f :+: makeRewrite dir g

class Discriminate fs t where
  discriminate :: t -> fs -> t

instance Discriminate (a -> a) [a] where
  discriminate x f = map f x

instance Discriminate g a => Discriminate (f :+: g) a where
  discriminate x (_ :+: g) = discriminate x g  

instance {-# OVERLAPPING #-} Discriminate ((a -> a) :+: g) [a] where
  discriminate x (f :+: g) = map f x

instance {-# OVERLAPPING #-} (Discriminate (fs :+: gs) a, Discriminate (fs :+: gs) b) => Discriminate (fs :+: gs) (a :+: b) where
  discriminate (a :+: b) fsgs = (discriminate a fsgs) :+: (discriminate b fsgs)

class Apply a b c | a -> b c where
  apply :: a -> b -> c

instance Apply (a -> b) a b where
  apply = ($)

instance {-# OVERLAPPING #-} Apply g b c' => Apply ((b -> c) :+: g) b (c :+: c') where
  apply (f :+: g) b = f b :+: apply g b
