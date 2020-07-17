{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Control.Monad.Can where

import Data.Kind (Type)
import Data.Can (Can (Non, Eno, One, Two))
import GHC.Generics (Generic1)
import Data.Functor.Classes (Eq1 (liftEq))
import Control.Applicative (liftA2, Alternative (empty, (<|>)))

-- Essentially, CanT m a b ~ ChronicleT a (MaybeT m) b
newtype CanT (m :: Type -> Type) (a :: Type) (b :: Type) =
  CanT { runCanT :: m (Can a b) }
  deriving (Generic1)

liftCanT :: (Functor m) => m b -> CanT m a b
liftCanT = CanT . fmap Eno

instance (Eq1 m, Eq a) => Eq1 (CanT m a) where
  liftEq f (CanT x) (CanT y) = liftEq go x y
    where
      go Non Non = True
      go (One x') (One y') = x' == y'
      go (Eno x') (Eno y') = f x' y'
      go (Two x' y') (Two x'' y'') = 
        x' == x'' && f y' y''
      go _ _ = False

-- etc

instance (Functor m) => Functor (CanT m a) where
  fmap f = CanT . fmap (fmap f) . runCanT

instance (Applicative m, Semigroup a) => Applicative (CanT m a) where
  pure = CanT . pure . Eno
  CanT fs <*> CanT xs = CanT (liftA2 (<*>) fs xs)

instance (Alternative m, Semigroup a) => Alternative (CanT m a) where
  empty = CanT empty
  CanT x <|> CanT y = CanT (x <|> y)
