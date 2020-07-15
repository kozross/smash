{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}

-- |
-- Module: Control.Monad.Smash
-- Copyright: (c) 20202 Koz Ross
-- License: BSD-3-Clause
--
-- Maintainer: Koz Ross <koz.ross@retro-freedom.nz>
-- Stability: Experimental
-- Portability: KindSignatures, LambdaCase, FlexibleInstances,
-- MultiParamTypeClasses, UndecidableInstances
--
-- Some prose will go here one day.
module Control.Monad.Smash (
  SmashT (..),
  liftSmashT)
  where

import GHC.Generics (Generic1)
import Control.Monad.Except (MonadError (throwError, catchError))
import Control.Monad.State (MonadState (get, put), gets)
import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (Bifunctor (bimap))
import Control.Monad.Zip (MonadZip (mzip))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (MonadPlus)
import Data.Kind (Type)
import Data.Smash (Smash (Smash, Nada), smash)
import Control.Applicative (liftA2, Alternative (empty, (<|>)))
import Data.Functor.Classes (Eq2 (liftEq2), Eq1 (liftEq), Ord1 (liftCompare))

-- Essentially SmashT m a b ~ EnvT a (MaybeT m) b
-- This way around, we can't be a MonadTrans, but we _can_ be a Bi*
newtype SmashT (m :: Type -> Type) (a :: Type) (b :: Type) = 
  SmashT { runSmashT :: m (Smash a b) }
  deriving (Generic1)

-- We can't be an instance of MonadTrans due to kindedness issues
liftSmashT :: (Monoid a, Functor m) => m b -> SmashT m a b
liftSmashT = SmashT . fmap (Smash mempty)

instance (Eq1 m, Eq a) => Eq1 (SmashT m a) where
  liftEq f (SmashT x) (SmashT y) = liftEq go x y
    where
      go Nada Nada = True
      go (Smash x' y') (Smash x'' y'') = 
        x' == x'' && f y' y''
      go _ _ = False

instance (Ord1 m, Ord a) => Ord1 (SmashT m a) where
  liftCompare f (SmashT x) (SmashT y) = liftCompare go x y
    where
      go Nada Nada = EQ
      go Nada _ = LT
      go _ Nada = GT
      go (Smash x' y') (Smash x'' y'') = 
        x' `compare` x'' <> f y' y''

-- etc etc

instance (Eq1 m) => Eq2 (SmashT m) where
  liftEq2 f g (SmashT x) (SmashT y) = liftEq go x y
    where
      go Nada Nada = True
      go (Smash x' y') (Smash x'' y'') = 
        f x' x'' && g y' y''
      go _ _ = False

-- etc etc

instance (Functor m) => Functor (SmashT m a) where
  fmap f = SmashT . fmap (fmap f) . runSmashT

instance (Applicative m, Monoid a) => Applicative (SmashT m a) where
  pure = SmashT . pure . Smash mempty
  SmashT fs <*> SmashT xs = SmashT (liftA2 (<*>) fs xs)

instance (Alternative m, Monoid a) => Alternative (SmashT m a) where
  empty = SmashT empty
  SmashT x <|> SmashT y = SmashT (x <|> y)

instance (Monad m, Monoid a) => Monad (SmashT m a) where
  x >>= f = SmashT $ do 
    sm <- runSmashT x
    case sm of
      Nada -> pure Nada
      Smash y z -> do
        sm' <- runSmashT (f z)
        case sm' of
          Nada -> pure Nada
          Smash y' z' -> pure . Smash (y <> y') $ z'

instance (Monad m, Monoid a) => MonadFail (SmashT m a) where
  fail _ = SmashT . pure $ Nada

instance (Alternative m, Monad m, Monoid a) => MonadPlus (SmashT m a)

instance (MonadIO m, Monoid a) => MonadIO (SmashT m a) where
  liftIO = SmashT . fmap (Smash mempty) . liftIO

instance (Monad m, Monoid a) => MonadZip (SmashT m a) where
  SmashT x `mzip` SmashT y = SmashT (go <$> x <*> y)
    where
      go Nada _ = Nada
      go _ Nada = Nada
      go (Smash x' y') (Smash x'' y'') = 
        Smash (x' <> x'') (y', y'')

instance (Foldable m) => Foldable (SmashT m a) where
  foldMap f = foldMap (smash mempty (\_ x -> f x)) . runSmashT

instance (Traversable m) => Traversable (SmashT m a) where
  traverse f = fmap SmashT . traverse go . runSmashT
    where 
      go = \case
        Nada -> pure Nada
        Smash x y -> Smash x <$> f y

instance (Functor m) => Bifunctor (SmashT m) where
  bimap f g = SmashT . fmap (bimap f g) . runSmashT

instance (Functor m, Foldable m) => Bifoldable (SmashT m) where
  bifoldMap f g = foldMap (bifoldMap f g) . runSmashT

instance (Functor m, Traversable m) => Bitraversable (SmashT m) where
  bitraverse f g = fmap SmashT . traverse (bitraverse f g) . runSmashT

instance (MonadReader r m, Monoid a) => MonadReader r (SmashT m a) where
  ask = SmashT $ asks (Smash mempty)
  local f = SmashT . local f . runSmashT

instance (MonadState s m, Monoid a) => MonadState s (SmashT m a) where
  get = SmashT $ gets (Smash mempty)
  put = SmashT . fmap (Smash mempty) . put

instance (MonadError e m, Monoid a) => MonadError e (SmashT m a) where
  throwError = SmashT . throwError
  catchError (SmashT comp) recover = 
    SmashT . catchError comp $ (runSmashT . recover)

-- MonadWriter is questionable (due to listen)
