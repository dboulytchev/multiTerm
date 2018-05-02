{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
--{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeFamilyDependencies #-}

infixr 6 :+:
infixr 6 :|:
  
data a :+: b = a :+: b
data a :|: b

-- Union of types

class Member x u

instance Member a a
instance Member a (a :|: b)  
instance Member a c => Member a (b :|: c)

-- End of union
-- Type of polyfunction

type family PolyFun u c = r | r -> u c where
  PolyFun (a :|: b) c = (a -> c) :+: PolyFun b c
  PolyFun  a        c = a -> c

-- End of polyfunction

-- Type-discriminated apply

class Apply f a b | f a -> b where
  apply :: f -> a -> b

instance Apply (a -> b) a b where
  apply = ($)

instance {-# OVERLAPPING #-} Apply ((a -> b) :+: g) a b where
  apply (f :+: _) x = apply f x

instance {-# OVERLAPPABLE #-} Apply g a b => Apply (f :+: g) a b where
  apply (_ :+: g) x = apply g x

--instance (f ~ PolyFun b c, SApply f a c, Member a b) => Apply f a c where
  --apply = sapply
  
-- End of apply

class List l a where
  polymap :: PolyFun a c -> l -> [c]

--instance (Member a b, List l b) => List (a :+: l) b where
  --polymap f (a :+: b) = apply f a : polymap f b
  
