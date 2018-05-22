{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}

module IntrospectionWorkout where

infixr 6 :+:
infixr 6 :|:

-- Product
data a :+: b = a :+: b

-- Coproduct
data a :|: b

-- Singleton
data U

type family Eithery u = r | r -> u where
  Eithery (a :|: b) = Either a (Eithery b)

class Prj u a where
  prj :: a -> Eithery u

instance {-# OVERLAPPING #-} Prj (a :|: b) a where
  prj a = Left a

instance {-# OVERLAPPABLE #-} Prj b c => Prj (a :|: b) c where
  prj a = Right (prj a)

{-class MultiPrj u where
  multiPrj :: Uniform u (Eithery u)

instance MultiPrj U where
  multiPrj = undefined

instance {-# OVERLAPPING #-} (Prj (a :|: b) a, MultiPrj b) => MultiPrj (a :|: b) where
  multiPrj = prj :+: multiPrj
-}

class MultiPrj u z where
  multiPrj :: Uniform u (Eithery z)

instance {-# OVERLAPPING #-} MultiPrj U U where
  multiPrj = undefined

instance {-# OVERLAPPING #-} (Prj (a :|: b) a, MultiPrj b (a :|: b)) => MultiPrj (a :|: b) (a :|: b) where
  multiPrj = prj :+: multiPrj

instance {-# OVERLAPPABLE #-} (MultiPrj b b, ComposeUniform b (Eithery b) (Either a (Eithery b))) => MultiPrj b (a :|: b) where
  multiPrj = composeUniform multiPrj Right

{-instance {-# OVERLAPPABLE #-} (c ~ b, MultiPrj c b) => MultiPrj b (a :|: b) where
  multiPrj = let (_ :+: x) = multiPrj in x-}

{-instance {-# OVERLAPPABLE #-} (z ~ (a :|: b), MultiPrj z z) => MultiPrj b z where
  multiPrj = let (_ :+: mprj) = (multiPrj :: Uniform z (Eithery z)) in mprj
-}
type family Reify u = r | r -> u where
  Reify (a :|: b) = [a] :+: Reify b

class Default u where
  def :: Reify u

instance Default U where
  def = undefined

instance Default b => Default (a :|: b) where
  def = [] :+: def

class Default u => Product u where
  insert :: [Eithery u] -> Reify u
  insert = foldl insert' def

  insert' :: Reify u -> Eithery u -> Reify u

instance Product U where
  insert' = undefined

instance Product b => Product (a :|: b) where
  insert' (as :+: bs) (Left  a) = (as ++ [a]) :+: bs
  insert' (as :+: bs) (Right b) = as :+: (insert' bs b)

reify :: (Product u, MultiPrj u u) => AppList u (Eithery u) -> Reify u
reify x = insert $ polymap multiPrj x


{-reify :: (Product u, MultiPrj u u) => AppList u (Eithery u) -> Reify u
reify x = insert $ polymap multiPrj x
-}


{-class ApplyReify a u where
  applyReify :: a -> Reify u -> Reify u

instance ApplyReify a (a :|: b) where
  applyReify a (as :+: bs) = ((as ++ [a]) :+: bs)

instance ApplyReify c b => ApplyReify c (a :|: b) where
  applyReify c (as :+: bs) = as :+: applyReify c bs
-}
-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c) -}
type family Uniform u c = r | r -> u c where
  Uniform (a :|: b) c = (a -> c) :+: Uniform b c
  --Uniform  U        c =
{-
class ShouldBeEasier b where
  shouldBeEasier :: Uniform b (Eithery b) -> Uniform b (Eithery (a :|: b))

instance ShouldBeEasier b where
  shouldBeEasier (f :+: fs) = (Right . f) :+: shouldBeEasier fs
-}
class ComposeUniform f b c where
  composeUniform :: Uniform f b -> (b -> c) -> Uniform f c

instance ComposeUniform U b c where
  composeUniform _ _ = undefined

instance ComposeUniform fs b c => ComposeUniform (f :|: fs) b c where
  composeUniform (f :+: fs) g = (\x -> g (f x) ) :+: (composeUniform fs g)


-- Type-discriminated application
class ApplyUniform f a b where
  applyUniform :: Uniform f b -> a -> b

instance {-# OVERLAPPING #-} ApplyUniform (a :|: c) a b where
  applyUniform (f :+: _) x = f x

instance  {-# OVERLAPPABLE #-} ApplyUniform y a b => ApplyUniform (x :|: y) a b where
  applyUniform (_ :+: g) x = applyUniform g x

--instance ApplyUniform (U a) a b where
--  applyUniform f x = f x

-- End of application

type family Transform u = r | r -> u where
  Transform (a :|: b) = (a -> a) :+: Transform b

class ApplyTransform u a where
  applyTransform :: Transform u -> a -> a

instance {-# OVERLAPPING #-}ApplyTransform (a :|: b) a where
  applyTransform (f :+: _) x = f x

instance {-# OVERlAPPABLE #-} ApplyTransform b c => ApplyTransform (a :|: b) c where
  applyTransform (_ :+: f) x = applyTransform f x

-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c -> t_i) -}
type family Polyform u c = r | r -> u c where
  Polyform (a :|: b) c = (a -> c -> a) :+: Polyform b c
--  Polyform (U a)     c = a -> c -> a

-- Type-discriminated application

class ApplyPolyform f a b where
  applyPolyform :: Polyform f b -> a -> b -> a

instance {-# OVERLAPPING #-} ApplyPolyform (a :|: c) a b where
  applyPolyform (f :+: _) x b = f x b

instance  {-# OVERLAPPABLE #-} ApplyPolyform y a b => ApplyPolyform (x :|: y) a b where
  applyPolyform (_ :+: g) x b = applyPolyform g x b

--instance ApplyPolyform (U a) a b where
--  applyPolyform f x b = f x b

-- End of application

-- Membership
{-
class Member x u where
  prj :: u -> x

instance {-# OVERLAPPING #-} Member a (a :|: b) where
  prj = unsafeCoerce

instance {-# OVERLAPPABLE #-} Member a c => Member a (b :|: c) where
  prj = unsafeCoerce
-}

data AppList f c = Nil | forall a . (Show a, ApplyUniform f a c, ApplyPolyform f a c, ApplyTransform f a) => Cons a (AppList f c)

instance Show (AppList f c) where
  show Nil = "[]"
  show (Cons h t) = show h ++ " : " ++ show t

polymap :: Uniform f c -> AppList f c -> [c]
polymap _ Nil = []
polymap f (Cons h t) = applyUniform f h : polymap f t

polyfoldl :: Uniform f (c -> c) -> AppList f (c -> c) -> c -> c
polyfoldl _  Nil       acc = acc
polyfoldl f (Cons h t) acc = polyfoldl f t (applyUniform f h acc)

polyfoldr :: Uniform f (c -> c) -> AppList f (c -> c) -> c -> c
polyfoldr _  Nil       acc = acc
polyfoldr f (Cons h t) acc = applyUniform f h (polyfoldr f t acc)

mapPolyForm :: Polyform f c -> AppList f c -> c -> AppList f c
mapPolyForm _ Nil _ = Nil
mapPolyForm f (Cons h t) c = Cons (applyPolyform f h c) (mapPolyForm f t c)

mapTransform :: Transform f -> AppList f c -> AppList f c
mapTransform _ Nil = Nil
mapTransform f (Cons h t) = Cons (applyTransform f h) (mapTransform f t)

main :: IO ()
main = do
  {-let (ints :+: _) = reify (Cons (42 :: Int) (Cons (13 :: Int) Nil)) :: Reify (Int :|: U)
  print $ ints
-}

  let (ints :+: strings :+: _) = reify (Cons (42 :: Int) (Cons "c" (Cons (13 :: Int) (Cons "abc" Nil)))) :: Reify (Int :|: String :|: U)
  print $ ints
  print $ strings

{-
  print $ polyfoldl ((\(x :: Int) acc -> x * acc :: Int) :+: (\x acc -> acc + length (x :: String) :: Int) :+: undefined) (Cons "b" (Cons (2 :: Int) (Cons "twitter" Nil))) 0
  print $ polyfoldr ((\(x :: Int) acc -> x * acc :: Int) :+: (\x acc -> acc + length (x :: String) :: Int) :+: undefined) (Cons "b" (Cons (2 :: Int) (Cons "twitter" Nil))) 0
-}
--p :: ExList -> String
--p Nil        = ""
--p (Cons h t) = show h ++ p t

--class List l a where
 -- polymap :: Uniform a c -> l -> [c]

--instance (ApplyUniformUniform b a b, List l b) => List (a :+: l) b where
  --polymap f (a :+: b) = applyUniform f a : polymap f b

