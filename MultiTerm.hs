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

  multiRewrite  :: (
                    MakeRewrite (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                    Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                    DiscriminateRewrite (Rewrite (Sub t)) (Sub t), 
                    Subtype t (Sub t)
                   ) => Direction -> Rewrite (Sub t) -> t -> t

  rewrite       :: (
                    LiftRewrite (t -> t) (Rewrite (Sub t)),
                    MakeRewrite (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                    Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                    DiscriminateRewrite (Rewrite (Sub t)) (Sub t), 
                    Subtype t (Sub t)
                   ) => Direction -> (t -> t) -> t -> t

  multiFold     :: (                           
                    MakeFold (Fold (Sub t) a) (ShallowFold (Sub t) a), 
                    Apply (ShallowFold (Sub t) a) (Fold (Sub t) a) (Fold (Sub t) a), 
                    DiscriminateFold (Fold (Sub t) a) a (Sub t), 
                    Subtype t (Sub t)
                   ) => Direction -> (Fold (Sub t) a) -> a -> t -> a


  fold          :: (                           
                    LiftFold (a -> t -> a) (Fold (Sub t) a),
                    MakeFold (Fold (Sub t) a) (ShallowFold (Sub t) a), 
                    Apply (ShallowFold (Sub t) a) (Fold (Sub t) a) (Fold (Sub t) a), 
                    DiscriminateFold (Fold (Sub t) a) a (Sub t), 
                    Subtype t (Sub t)
                   ) => Direction -> (a -> t -> a) -> a -> t -> a

  fv            :: (                   
                    Eq (Var t),
                    MakeFV (Fold (Sub t) [Var t]),
                    MakeFold {-BottomUp-} (Fold (Sub t) [Var t]) (ShallowFold (Sub t) [Var t]), 
                    Apply (ShallowFold (Sub t) [Var t]) (Fold (Sub t) [Var t]) (Fold (Sub t) [Var t]), 
                    DiscriminateFold (Fold (Sub t) [Var t]) [Var t] (Sub t), 
                    Subtype t (Sub t)
                   ) => t -> [Var t]

  subst         :: (
                    Eq (Var t),
                    LiftRewrite (t -> t) (Rewrite (Sub t)),
                    MakeRewrite {-BottomUp-} (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                    Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                    DiscriminateRewrite (Rewrite (Sub t)) (Sub t), 
                    Subtype t (Sub t)
                   ) => t -> Var t -> t -> t

  cas           :: (
                    Eq (Var t),
                    LiftRewrite (t -> t) (Rewrite (Sub t)),
                    MakeRewrite {-TopDown-} (Rewrite (Sub t)) (ShallowRewrite (Sub t)), 
                    Apply (ShallowRewrite (Sub t)) (Rewrite (Sub t)) (Rewrite (Sub t)), 
                    DiscriminateRewrite (Rewrite (Sub t)) (Sub t), 
                    Subtype t (Sub t)
                   ) => [Var t] -> t -> Var t -> t -> t

  multiRewrite d f t = 
    let fs = apply (makeRewrite d f :: ShallowRewrite (Sub t)) fs in 
    case d of
      BottomUp -> let t' = make t $ discriminateRewrite (subterms t) fs in
                  ((prj $ discriminateRewrite (inj t' :: Sub t) f) :: t) 
      _        -> let t' = ((prj $ discriminateRewrite (inj t :: Sub t) f) :: t) in
                  make t' $ discriminateRewrite (subterms t') fs

  rewrite d f t = multiRewrite d (liftRewrite f) t

  multiFold d f (a :: a) t = 
    let fs = apply (makeFold d f :: ShallowFold (Sub t) a) fs in
    case d of
      BottomUp -> discriminateFold (inj t :: Sub t) (discriminateFold (subterms t) a fs) f
      _        -> discriminateFold (subterms t) (discriminateFold (inj t :: Sub t) a fs) fs     


  fold d f (a :: a) t = multiFold d (liftFold f) a t

  fv t = nub $ multiFold BottomUp (makeFV :: Fold (Sub t) [Var t]) [] t

  subst t x s = rewrite BottomUp (\ t' -> case var t' of
                                            Just y -> if y == x then s else t'
                                            _      -> t'
                                 ) t
{-
  cas vs t x s = subst (rename t [] $ fv s) x s where
    rename t rs fvs = rewriteTopDown
      


rewriteTopDown (\ t' -> case var t' of
                                           Just y -> if y == x then s else t'
                                           _      -> t'
                                ) t             
-}
 
data Direction = TopDown | BottomUp

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
  Rewrite [t]         = t -> t
  Rewrite ([t] :+: b) = (t -> t) :+: Rewrite b

type family Fold t a where
  Fold [t] a         = a -> t -> a
  Fold ([t] :+: b) a = (a -> t -> a) :+: Fold b a

type family LiftForRewrite a where
  LiftForRewrite [f]       = (f -> f) -> f -> f
  LiftForRewrite (a :+: b) = Dom (LiftForRewrite a) :+: Dom (LiftForRewrite b) -> Cod (LiftForRewrite a) :+: Cod (LiftForRewrite b)

type family LiftForFold t a where
  LiftForFold [t]       a = (a -> t -> a) -> a -> t -> a
  LiftForFold (a :+: b) c = Dom (LiftForFold a c) :+: Dom (LiftForFold b c) -> Cod (LiftForFold a c) :+: Cod (LiftForFold b c)

type family Distrib a where
  Distrib (c -> a :+: b) = (c -> a) :+: (c -> b)
  Distrib (c -> a)       = c -> a

type family ShallowRewrite a where
  ShallowRewrite a = Distrib (LiftForRewrite a)

type family ShallowFold a b where
  ShallowFold a b = Distrib (LiftForFold a b)

class LiftRewrite f fs where
  liftRewrite :: f -> fs

instance LiftRewrite (t -> t) (a -> a) where
  liftRewrite f t = t

instance {-# OVERLAPPING #-} LiftRewrite (t -> t) (t -> t) where
  liftRewrite f x = f x
  
instance (LiftRewrite f fs, LiftRewrite f gs) => LiftRewrite f (fs :+: gs) where
  liftRewrite f = liftRewrite f :+: liftRewrite f

class LiftFold f fs where
  liftFold :: f -> fs

instance LiftFold (a -> t -> a) (a -> x -> a) where
  liftFold f = \ a t -> a

instance {-# OVERLAPPING #-} LiftFold (a -> t -> a) (a -> t -> a) where
  liftFold f = \ a x -> f a x
  
instance (LiftFold f fs, LiftFold f gs) => LiftFold f (fs :+: gs) where
  liftFold f = liftFold f :+: liftFold f

class MakeRewrite f fs where
  makeRewrite :: Direction -> f -> fs

instance (DiscriminateRewrite c (Sub t), Term t) => MakeRewrite (t -> t) (c -> t -> t) where
  makeRewrite dir f c = case dir of
                          BottomUp -> \ t -> f $ make t $ discriminateRewrite (subterms t) c
                          _        -> \ t -> let t' = f t in make t' $ discriminateRewrite (subterms t') c

instance {-# OVERLAPPING #-} (MakeRewrite f fs, MakeRewrite g gs) => MakeRewrite (f :+: g) (fs :+: gs) where
  makeRewrite dir (f :+: g) = makeRewrite dir f :+: makeRewrite dir g

class MakeFold f fs where
  makeFold :: Direction -> f -> fs

instance (DiscriminateFold c a (Sub t), Term t) => MakeFold (a -> t -> a) (c -> a -> t -> a) where
  makeFold dir f c = case dir of
                       BottomUp -> \ a t -> f (discriminateFold (subterms t) a c) t
                       _        -> \ a t -> discriminateFold (subterms t) (f a t) c

instance {-# OVERLAPPING #-} (MakeFold f fs, MakeFold g gs) => MakeFold (f :+: g) (fs :+: gs) where
  makeFold dir (f :+: g) = makeFold dir f :+: makeFold dir g

class DiscriminateFold fs a t where
  discriminateFold :: t -> a -> fs -> a

instance DiscriminateFold (a -> b -> a) a [b] where
  discriminateFold x a f = foldl f a x

instance DiscriminateFold g b a => DiscriminateFold (f :+: g) b a where
  discriminateFold x a (_ :+: g) = discriminateFold x a g  

instance {-# OVERLAPPING #-} DiscriminateFold ((a -> b -> a) :+: g) a [b] where
  discriminateFold x a (f :+: g) = foldl f a x

instance {-# OVERLAPPING #-} (DiscriminateFold (fs :+: gs) c a, DiscriminateFold (fs :+: gs) c b) => DiscriminateFold (fs :+: gs) c (a :+: b) where
  discriminateFold (a :+: b) c fsgs = (discriminateFold b (discriminateFold a c fsgs) fsgs)

class DiscriminateRewrite fs t where
  discriminateRewrite :: t -> fs -> t

instance DiscriminateRewrite (a -> a) [a] where
  discriminateRewrite x f = map f x

instance DiscriminateRewrite g a => DiscriminateRewrite (f :+: g) a where
  discriminateRewrite x (_ :+: g) = discriminateRewrite x g  

instance {-# OVERLAPPING #-} DiscriminateRewrite ((a -> a) :+: g) [a] where
  discriminateRewrite x (f :+: g) = map f x

instance {-# OVERLAPPING #-} (DiscriminateRewrite (fs :+: gs) a, DiscriminateRewrite (fs :+: gs) b) => DiscriminateRewrite (fs :+: gs) (a :+: b) where
  discriminateRewrite (a :+: b) fsgs = (discriminateRewrite a fsgs) :+: (discriminateRewrite b fsgs)

class Apply a b c | a -> b c where
  apply :: a -> b -> c

instance Apply (a -> b) a b where
  apply = ($)

instance {-# OVERLAPPING #-} Apply g b c' => Apply ((b -> c) :+: g) b (c :+: c') where
  apply (f :+: g) b = f b :+: apply g b

class MakeFV fs where
  makeFV :: fs

instance (Eq v, Term t, v ~ Var t) => MakeFV ([v] -> t -> [v]) where
  makeFV a t = case var t of
                 Just  v -> v : a
                 Nothing -> case binder t of
                              Just v  -> filter (/= v) a
                              Nothing -> a

instance (MakeFV f, MakeFV g) => MakeFV (f :+: g) where
  makeFV = makeFV :+: makeFV 

