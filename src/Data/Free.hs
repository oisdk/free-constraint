{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE UnicodeSyntax     #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Free
  ( FreeT
  , runFreeT
  , foldFreeT
  , pattern FreeT
  , Free
  , runFree
  , foldFree
  , pattern Free
  ) where

import           Control.Applicative
import           Control.Monad.Cont
import           Control.Monad.Identity
import           Data.Coerce
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Semigroup
import           GHC.Exts                  hiding (toList)
import qualified GHC.Exts                  as Exts

newtype Sequence f a = Sequence
    { unSequence :: f a
    } deriving (Functor,Applicative,Monad,Foldable)

instance (Applicative f, Semigroup a) =>
         Semigroup (Sequence f a) where
    (<>) =
        (coerce :: (f a -> f a -> f a) -> Sequence f a -> Sequence f a -> Sequence f a)
            (liftA2 (<>))
    {-# INLINE (<>) #-}

instance (Applicative f, Monoid a) =>
         Monoid (Sequence f a) where
    mempty = Sequence (pure mempty)
    {-# INLINE mempty #-}
    mappend =
        (coerce :: (f a -> f a -> f a) -> Sequence f a -> Sequence f a -> Sequence f a)
            (liftA2 mappend)
    {-# INLINE mappend #-}
newtype FreeT c m a
  = FreeT_
  { unFreeT_ :: ∀ b. c b => ContT b m a }

runFreeT :: FreeT c m a -> (∀ b. c b => (a -> m b) -> m b)
runFreeT c = runContT (unFreeT_ c)

pattern FreeT :: (∀ b. c b => (a -> m b) -> m b) -> FreeT c m a
pattern FreeT c <- (runFreeT -> c) where
  FreeT c = FreeT_ (ContT c)

foldFreeT :: c b => (a -> m b) -> FreeT c m a -> m b
foldFreeT = flip runFreeT
{-# INLINE foldFreeT #-}

instance Functor (FreeT c m) where
  fmap f (FreeT_ x) = FreeT_ (fmap f x)
  {-# INLINE fmap #-}

instance Applicative (FreeT c m) where
  pure x = FreeT_ (pure x)
  {-# INLINE pure #-}
  FreeT_ fs <*> FreeT_ xs = FreeT_ (fs <*> xs)
  {-# INLINE (<*>) #-}

instance Monad (FreeT c m) where
  FreeT_ x >>= f = FreeT_ (x >>= (unFreeT_ . f))

instance (Foldable m, Applicative m) => Foldable (FreeT Monoid m) where
  foldMap f = fold . foldFreeT (pure . f)

instance (Foldable m, Applicative m) => Foldable (FreeT Semigroup m) where
  foldMap f = unwrapMonoid .# fold . foldFreeT (pure . WrapMonoid .# f)

type Free c = FreeT c Identity

runFree :: Free c a -> (∀ b. c b => (a -> b) -> b)
runFree (FreeT_ c) = runCont c
{-# INLINE runFree #-}

foldFree :: c b => (a -> b) -> Free c a -> b
foldFree = flip runFree
{-# INLINE foldFree #-}

instance Foldable (Free Semigroup) where
  foldMap f = unwrapMonoid .# foldFree (WrapMonoid .# f)
  {-# INLINE foldMap #-}

instance Applicative m => Monoid (FreeT Monoid m a) where
  mempty = FreeT (const (pure mempty))
  {-# INLINE mempty #-}
  mappend (FreeT x) (FreeT y) = FreeT (\f -> liftA2 mappend (x f) (y f))
  {-# INLINE mappend #-}

instance Applicative m => Semigroup (FreeT Monoid m a) where
  (<>) (FreeT x) (FreeT y) = FreeT (\f -> liftA2 mappend (x f) (y f))

instance Applicative m => Semigroup (FreeT Semigroup m a) where
  (<>) (FreeT x) (FreeT y) = FreeT (\f -> liftA2 (<>) (x f) (y f))

pattern Free :: (∀ b. c b => (a -> b) -> b) -> Free c a
pattern Free c <- (runFree -> c) where
  Free c = FreeT_ (cont c)

collapse :: Monad m => m (FreeT c m a) -> FreeT c m a
collapse = join . lift

instance MonadTrans (FreeT c) where
  lift x = FreeT_ (lift x)
  {-# INLINE lift #-}

instance (Monad m, Traversable m) =>
         Traversable (FreeT Monoid m) where
    traverse f (FreeT xs) =
        (fmap collapse . traverse unSequence . xs)
            (pure . fmap pure . Sequence .# f)
    {-# INLINE traverse #-}

instance (Monad m, Traversable m) =>
         Traversable (FreeT Semigroup m) where
    traverse f (FreeT xs) =
        (fmap collapse . traverse unSequence . xs)
            (pure . fmap pure . Sequence .# f)
    {-# INLINE traverse #-}

instance Alternative f => Alternative (FreeT c f) where
  empty = FreeT (const empty)
  {-# INLINE empty #-}
  FreeT f <|> FreeT g = FreeT (\x -> f x <|> g x)
  {-# INLINE (<|>) #-}

instance (Applicative f, Foldable f) => IsList (FreeT Monoid f a) where
  type Item (FreeT Monoid f a) = a
  fromList xs = FreeT $ \f -> (unSequence .# foldMap (Sequence .# f)) xs
  toList = toList

instance (Eq1 m, Applicative m) =>
         Eq1 (FreeT Monoid m) where
    liftEq eq xs ys =
        liftEq
            (\x y ->
                  and $ zipWith eq x y)
            (toListM xs)
            (toListM ys)

instance (Ord1 m, Applicative m) =>
         Ord1 (FreeT Monoid m) where
    liftCompare cmp xs ys =
        liftCompare
            (\x y ->
                  fold $ zipWith cmp x y)
            (toListM xs)
            (toListM ys)

toListM :: Applicative m => FreeT Monoid m a -> m [a]
toListM = fmap (($[]) . appEndo) . foldFreeT (pure . Endo .# (:))

instance (Eq1 m, Applicative m, Eq a) => Eq (FreeT Monoid m a) where
  (==) = eq1

instance (Ord1 m, Applicative m, Ord a) => Ord (FreeT Monoid m a) where
  compare = compare1

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce
