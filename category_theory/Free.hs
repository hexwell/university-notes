{-# LANGUAGE GADTs #-}
-- MONADS A LA CARTE

import Prelude hiding (Functor(..), Monad(..))

-- Most important effects of State st are:
-- 1. GET yields a value of type st
-- 2. PUT takes as input a value of type st and produces ()

type St = Integer

data StateI a where
  Get :: StateI St
  Put :: St -> StateI ()
  PutStrLn :: String -> StateI ()
-- Note: There are no values of type "StateI Char".
-- Note: StateI is not a functor,
-- how would you implement
-- fmap :: (a -> b) -> StateI a -> StateI b?

restrictedmap :: (St -> St) -> StateI St -> StateI St
restrictedmap _ Get = Get

-- StateI is a type constructor
-- (its kind is Type -> Type),
-- but NOT a functor.
-- So let's construct the "free functor over StateI"!

-- FreeF t is the free functor over the type constructor t
data FreeF t a = forall r. Mk (t r) (r -> a)

class Functor f where
  fmap :: (a -> b) -> (f a -> f b)
-- Remark: In case that fmap id = id, then
-- fmap (f . g) = fmap f . fmap g. Because
-- of "theorems for free".

instance Functor (FreeF t) where
  fmap f (Mk x g) = Mk x (f . g)
  --   ^     ^ ^               ^
  --   a -> b| +----- r -> a   +----- r -> b
  --         |
  --         t r

-- "FreeM f" is the free monad over the functor f.
-- "FreeM f a" is the type of f-shaped trees
-- with leaves decorated with values of type a.
data FreeM f a = Pure a | Roll (f (FreeM f a))

type Prog t a = FreeM (FreeF t) a

put :: St -> Prog StateI ()
put st' = Roll (Mk (Put st') (\_ -> Pure ()))

putstrln :: String -> Prog StateI ()
putstrln str = Roll (Mk (PutStrLn str) (\_ -> Pure ()))

get :: Prog StateI St
get = Roll (Mk Get (\st -> Pure st))

(>>) :: (Monad m) => m a -> m b -> m b
m >> n = m >>= (\_ -> n)

exampleProgram :: Prog StateI Float
exampleProgram = get >>= (\st -> put (st + 1) >> return 42)

interpret :: Prog StateI a -> (St -> (a,St))
interpret (Pure x) st = (x,st)
interpret (Roll (Mk Get f)) st = interpret (f st) st
interpret (Roll (Mk (Put st') f)) st = interpret (f ()) st'
interpret (Roll (Mk (PutStrLn str) f)) st = interpret (f ()) st

class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b

instance (Functor f) => Functor (FreeM f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Roll u) = Roll (fmap (fmap f) u)

instance (Functor f) => Monad (FreeM f) where
  return = Pure
  Pure x >>= f = f x
  Roll u >>= f = Roll (fmap (>>= f) u)

{-
data Void a
-- FreeM Void a is isomorphic to a
iso :: FreeM Void a -> a
iso (Pure x) = x

type Pair a = (a,a)
-- FreeM Pair a is the type of binary trees with
-- leaves decorated by values of type a

data Unit a = MkUnit
-- FreeM Unit a is isomorphic to Maybe a
iso' :: FreeM Unit a -> Maybe a
iso' (Pure x)      = Just x
iso' (Roll MkUnit) = Nothing

type Nat = Integer  -- I mean only the >= 0 ones.
iso'' :: FreeM Maybe a -> (Nat, a)
iso'' = undefined

data Number = forall r. (Num r, Show r) => MkNum r

show' :: Number -> String
show' (MkNum a) = show a

neg :: Number -> Number
neg (MkNum a) = MkNum (negate a)

{-
x :: Number
x = MkNum (3 :: Int)

y :: Number
y = MkNum (3.0 :: Double)
-}
{-
newtype State st a = MkState (st -> (a,st))

get :: State st st
get = MkState $ \st -> (st,st)

put :: st -> State st ()
put st' = MkState $ \st -> ((),st')

test = get >>= (\x -> put (x + 1) >> (get >>= (\x -> put (x + 3))))
-}
-}
