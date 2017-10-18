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
  subterms :: t -> Sub t
  var      :: t -> Maybe (Var t)
  binder   :: t -> Maybe (Var t)
  eq       :: t -> t -> Bool
  make     :: t -> Sub t -> t
  hom      :: (MakeHom (t -> t) (Distrib (Lift (Sub t))), Apply (Distrib (Lift (Sub t))) (Hom (Sub t)) (Hom (Sub t)), Choose (Hom (Sub t)) (Sub t), Term t) => (t -> t) -> t -> t
  hom f t = 
    let s  = subterms t in   
    let fs = apply (makeHom (hom f) :: Distrib (Lift (Sub t))) fs in
    f $ make t $ choose s fs

infixr 5 :+:

data h :+: t = h :+: t deriving Show

type family Dom a where
  Dom (a -> b) = a

type family Cod a where
  Cod (a -> b) = b

type family Hom a where
  Hom [f]         = f -> f
  Hom ([a] :+: b) = (a -> a) :+: Hom b

type family Lift a where
  Lift [f]       = (f -> f) -> f -> f
  Lift (a :+: b) = (Dom (Lift a) :+: Dom (Lift b) -> Cod (Lift a) :+: Cod (Lift b))

lift :: a -> Lift a
lift = undefined

type family Distrib a where
  Distrib (c -> a :+: b) = (c -> a) :+: (c -> b)
  Distrib (c -> a)       = c -> a

distrib :: a -> Distrib a
distrib = undefined

class MakeHom0 f fs where
  makeHom0 :: f {- -> fs-} -> fs

instance (Choose c (Sub a), Term a) => MakeHom0 (t -> t) (c -> a -> a) where
  makeHom0 f {-_-} c t = make t $ choose (subterms t) c

instance {-# OVERLAPPING #-} (Choose c (Sub t), Term t) => MakeHom0 (t -> t) (c -> t -> t) where
  makeHom0 f {-_-} _ x = f x

class MakeHom f fs where
  makeHom :: f {--> fs-} -> fs

instance MakeHom0 f fs => MakeHom f fs where
  makeHom = makeHom0

instance {-# OVERLAPPING #-} (MakeHom0 f fs, MakeHom f gs) => MakeHom f (fs :+: gs) where
  makeHom f {-(fs :+: gs)-} = (makeHom0 f {-fs-}) :+: (makeHom f {-gs-})

class Choose fs t where
  choose :: t -> fs -> t

instance Choose (a -> a) [a] where
  choose x f = map f x

instance Choose g a => Choose (f :+: g) a where
  choose x (_ :+: g) = choose x g  

instance {-# OVERLAPPING #-} Choose ((a -> a) :+: g) [a] where
  choose x (f :+: g) = map f x

instance {-# OVERLAPPING #-} (Choose (fs :+: gs) a, Choose (fs :+: gs) b) => Choose (fs :+: gs) (a :+: b) where
  choose (a :+: b) fsgs = (choose a fsgs) :+: (choose b fsgs)

class Apply a b c | a -> b c where
  apply :: a -> b -> c

instance Apply (a -> b) a b where
  apply = ($)

instance {-# OVERLAPPING #-} Apply g b c' => Apply ((b -> c) :+: g) b (c :+: c') where
  apply (f :+: g) b = f b :+: apply g b
