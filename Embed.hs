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

module Embed where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm

class (Term t, MergeUniforms (Sub t)) => FlatEmbed t where
  flatCouple :: t -> Uniform (Sub t) Bool
  flatDiving :: t -> Uniform (Sub t) Bool
  flatEmbed  :: t -> Uniform (Sub t) Bool

  flatEmbed t = mergeUniforms (flatCouple t) (flatDiving t) (||)

class CompleteFlatEmbed u v where
  completeFlatEmbed :: Uniform u (Uniform v Bool)

instance CompleteFlatEmbed U v where
  completeFlatEmbed = undefined

instance (FlatEmbed a, v ~ Sub a, CompleteFlatEmbed b v) => CompleteFlatEmbed (a :|: b) v where
  completeFlatEmbed = flatEmbed :+: completeFlatEmbed


class (Sub t ~ Sub s,
       CompleteFlatEmbed (Sub t) (Sub s),
       ApplyUniform (Sub t) t,
       ApplyUniform (Sub s) s,
       LiftEmbed (Sub s) (Sub s) (Sub s),
       MakeEmbedder (Sub s) (Sub s) (Sub s) (Sub s)) => Embed t s where
  embed :: t -> s -> Bool
  embed t s =
    let fs = makeEmbedder liftEmbed fs completeFlatEmbed in
    applyUniform (applyUniform fs t :: Uniform (Sub s) Bool) s


type family ShallowEmbedder t s u v where
  ShallowEmbedder t s u v = Uniform u (Uniform v Bool) -> Uniform u (Uniform v Bool) -> t -> s -> Bool

class ShallowEmbed t s where
  shallowEmbed :: ShallowEmbedder t s (Sub t) (Sub s)

instance ( Term t, Term s,
           Sub t ~ Sub s,
           ApplyUniform (Sub s) s, ApplyUniform (Sub t) t
         ) => ShallowEmbed t s where
  shallowEmbed deep shallow t s =
    applyUniform (applyUniform shallow t) s &&
      (
        let t_subs = subterms t in
        let s_subs = subterms s in
        heteroLength t_subs == heteroLength s_subs && (and $ heteroZipWith deep t_subs s_subs)
      )

type family HelperEmbedder t u v w = r | r -> t u v w where
  HelperEmbedder t u v w = Uniform u (Uniform v Bool) -> Uniform u (Uniform v Bool) -> t -> (Uniform w Bool)

class HelperEmbed t u v w where
  helperEmbed :: HelperEmbedder t u v w

instance HelperEmbed t u v U where
  helperEmbed _ _ _ = undefined

instance (ShallowEmbed t a, HelperEmbed t u v b, u ~ Sub t, v ~ Sub a) => HelperEmbed t u v (a :|: b) where
  helperEmbed deep shallow t =
    (shallowEmbed deep shallow t) :+: helperEmbed deep shallow t


type family LiftEmbedder ab u v w = r | r -> ab u v w  where
  LiftEmbedder (a :|: b) u v w = HelperEmbedder a u v w :+: LiftEmbedder b u v w

class LiftEmbed ab u w where
  liftEmbed :: LiftEmbedder ab u u w

instance LiftEmbed U u w where
  liftEmbed = undefined

instance (HelperEmbed a u u w, LiftEmbed b u w) => LiftEmbed (a :|: b) u w  where
  liftEmbed = helperEmbed :+: liftEmbed

class MakeEmbedder n u v m where
  makeEmbedder :: LiftEmbedder n u v m -> Uniform u (Uniform v Bool) -> Uniform u (Uniform v Bool) -> Uniform n (Uniform m Bool)

instance MakeEmbedder U u v m where
  makeEmbedder _ _ _ = undefined

instance (MakeEmbedder b u v m) => MakeEmbedder (a :|: b) u v m where
  makeEmbedder (p :+: q) a b =
    let f = p a b in
    let g = makeEmbedder q a b in
    f :+: g