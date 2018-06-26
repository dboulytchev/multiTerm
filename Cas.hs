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

module Cas where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm
import Data.List ((\\), nub, concat, delete)
import Data.Maybe

type family CasSubst t where
  CasSubst t = ([Var t], Var t -> t, [Var t])

class ( Eq (Var t), Term t, FreeVars t,
        MakeFv (Sub t) (Var t),             -- \
        LiftFold (Sub t) (Sub t) [Var t],   -- | These come from FreeVars t
        MakeFolder (Sub t) (Sub t) [Var t], -- |
        ApplyUniform (Sub t) t              -- /
      ) => CAS t where
  freshVar :: [Var t] -> (Var t, t)
  rename :: t -> Var t -> t

  singleton :: Var t -> t -> CasSubst t
  singleton v t =
    ([v], update empty v t, freeVars t)
    where
      empty _ = undefined
      update f x a y = if x == y then a else f y

  cas' :: t -> CasSubst t -> (t, CasSubst t)
  cas' term subst@(dom, s, fvs) =
    case var term of
      Just v  -> (if v `elem` dom then s v else term, ([], s, fvs))
      Nothing ->
        case binder term of
          Nothing -> (term, subst)
          Just b  ->
            if b `elem` dom
            then (term, (dom \\ [b], s, fvs))
            else if b `elem`  fvs
                 then let (v, z) = freshVar (b : fvs) :: (Var t, t) in
                      (rename term v, (b : dom, update s b z, v : fvs))
                 else (term, subst)
    where
      update f x a y = if x == y then a else f y
      extend (dom, s, fvs) x a = (nub x:dom, update s x a, nub $ (freeVars a ++ fvs))

  cas :: (
           ApplyPairform (Sub t) t,
           FlatCas (Sub t) t t,
           LiftCas (Sub t) (Sub t) t,
           MakeCaser (Sub t) (Sub t) t
         ) => t -> Var t -> t -> t
  cas subj x t =
    let fs = makeCaser liftCas fs (flatCas t) :: Pairform (Sub t) (CasSubst t) in
    fst $ applyPairform fs subj (singleton x t)

class FlatCas u t subst where
  flatCas :: t -> Pairform u (CasSubst subst)

instance FlatCas U t subst where
  flatCas _ = undefined

instance {-# OVERLAPPING #-} (CAS a, FlatCas b a a) => FlatCas (a :|: b) a a where
  flatCas t = cas' :+: flatCas t

instance {-# OVERLAPPABLE #-} FlatCas b t subst =>  FlatCas (a :|: b) t subst where
  flatCas t = (,) :+: flatCas t


type family ShallowCaser u t subst = r | r -> u t where
  ShallowCaser u t subst = Pairform u (CasSubst subst) -> Pairform u (CasSubst subst) -> t -> CasSubst subst -> (t, CasSubst subst)

class Term t => ShallowCas t subst where
  shallowCas :: ShallowCaser (Sub t) t subst

instance (Term t, ApplyPairform (Sub t) t) => ShallowCas t subst where
  shallowCas deep shallow t subst =
    let (t', subst'@(dom, _, _)) = applyPairform shallow t subst in
    let subs = if null dom then subterms t' else mapPairform deep (subterms t') subst' in
    (make t' subs, subst')

class MakeCaser t g subst where
  makeCaser :: LiftCaser t g subst -> Pairform g (CasSubst subst) -> Pairform g (CasSubst subst) -> Pairform t (CasSubst subst)

instance MakeCaser U g subst where
  makeCaser _ _ _ = undefined

instance  (MakeCaser b g subst) => MakeCaser (a :|: b) g subst where
  makeCaser (t :+: q) a b =
    let f = t a b in
    let g = makeCaser q a b in
    f :+: g

type family LiftCaser t g subst = r | r -> t g subst where
  LiftCaser (a :|: b) g subst = ShallowCaser g a subst :+: LiftCaser b g subst

class LiftCas t g subst where
  liftCas :: LiftCaser t g subst

instance LiftCas U g subst where
  liftCas = undefined

instance (ApplyPairform g a, Term a, g ~ Sub a, LiftCas b g subst) =>  LiftCas (a :|: b) g subst where
  liftCas = shallowCas :+: liftCas