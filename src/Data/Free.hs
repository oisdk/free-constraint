{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | A module for the free functor over some class. The type can be thought og
-- as this:
--
-- > newtype Free c a = Free { runFree :: ∀ b. c b => (a -> b) -> b }
--
-- However, it is provided as a transformer.
module Data.Free
  (
   -- * FreeT Monad Transformer
   FreeT
  ,runFreeT
  ,foldFreeT
  ,pattern FreeT
  ,
   -- * Free constrained monad
   Free
  ,runFree
  ,foldFree
  ,pattern Free)
  where

import           Control.Monad.Trans
import           Control.Monad.State.Class
import           Control.Monad.Reader.Class

import           Control.Applicative

import           Control.Monad.Cont     as Cont
import           Control.Monad.Identity

import           Data.Coerce
import           Data.Foldable
import           Data.Semigroup

import           Data.Functor.Classes

import           GHC.Exts               hiding (toList)
import qualified GHC.Exts               as Exts

newtype Sequence f a = Sequence
    { unSequence :: f a
    } deriving (Functor,Applicative,Monad,Foldable)

instance (Applicative f, Semigroup a) =>
         Semigroup (Sequence f a) where
    (<>) =
        (coerce
           :: (f a -> f a -> f a) -> Sequence f a -> Sequence f a -> Sequence f a)
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

-- | The free monad over some class c. This can be used to implement various
-- data structures: the free monoid, for instance, is a list-like structure
-- with /O(1)/ concatenation. The free semigroup is similar.
--
-- The implementation is 'ContT' under the hood, but that is hidden from the
-- user with newtypes and pattern synonyms.
newtype FreeT c m a
  = FreeT_
  { unFreeT_ :: ∀ b. c b => ContT b m a }

-- | Run a free computation.
runFreeT :: FreeT c m a -> (∀ b. c b => (a -> m b) -> m b)
runFreeT c = runContT (unFreeT_ c)
{-# INLINE runFreeT #-}

-- | This pattern is
pattern FreeT :: (∀ b. c b => (a -> m b) -> m b) -> FreeT c m a
pattern FreeT c <- (runFreeT -> c) where
  FreeT c = FreeT_ (ContT c)

-- | Fold a free according to its class.
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
  {-# INLINE (>>=) #-}

instance (Foldable m, Applicative m) => Foldable (FreeT Monoid m) where
  foldMap f = fold . foldFreeT (pure . f)

instance (Foldable m, Applicative m) => Foldable (FreeT Semigroup m) where
  foldMap f = unwrapMonoid .# fold . foldFreeT (pure . WrapMonoid .# f)

-- | The free functor in the non-transformer
type Free c = FreeT c Identity

-- | Run a free computation.
runFree :: Free c a -> (∀ b. c b => (a -> b) -> b)
runFree (FreeT_ c) = runCont c
{-# INLINE runFree #-}

-- | Fold a free. For the free monoid, this is 'foldMap'.
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
  {-# INLINE (<>) #-}

instance Applicative m => Semigroup (FreeT Semigroup m a) where
  (<>) (FreeT x) (FreeT y) = FreeT (\f -> liftA2 (<>) (x f) (y f))
  {-# INLINE (<>) #-}

-- | This pattern behaves as if
pattern Free :: (∀ b. c b => (a -> b) -> b) -> Free c a
pattern Free c <- (runFree -> c) where
  Free c = FreeT_ (cont c)

collapse :: Monad m => m (FreeT c m a) -> FreeT c m a
collapse = join . lift
{-# INLINE collapse #-}

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

instance (Eq1 m, Applicative m) =>
         Eq1 (FreeT Semigroup m) where
    liftEq eq xs ys =
        liftEq
            (\x y ->
                  and $ zipWith eq x y)
            (toListS xs)
            (toListS ys)

instance (Ord1 m, Applicative m) =>
         Ord1 (FreeT Semigroup m) where
    liftCompare cmp xs ys =
        liftCompare
            (\x y ->
                  fold $ zipWith cmp x y)
            (toListS xs)
            (toListS ys)

toListM :: Applicative m => FreeT Monoid m a -> m [a]
toListM = fmap (($[]) . appEndo) . foldFreeT (pure . Endo .# (:))

toListS :: Applicative m => FreeT Semigroup m a -> m [a]
toListS = fmap (($[]) . appEndo) . foldFreeT (pure . Endo .# (:))

instance (Eq1 m, Applicative m, Eq a) =>
         Eq (FreeT Monoid m a) where
    (==) = eq1

instance (Ord1 m, Applicative m, Ord a) =>
         Ord (FreeT Monoid m a) where
    compare = compare1

instance (Eq1 m, Applicative m, Eq a) =>
         Eq (FreeT Semigroup m a) where
    (==) = eq1

instance (Ord1 m, Applicative m, Ord a) =>
         Ord (FreeT Semigroup m a) where
    compare = compare1

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce

instance MonadState s m => MonadState s (FreeT r m) where
    get = lift get
    put = lift . put
    state = lift . state

instance MonadReader r m => MonadReader r (FreeT c m) where
    ask   = lift ask
    local = liftLocal ask local
    reader = lift . reader

liftLocal
    :: (Monad m)
    => m r'
    -> (∀ r. c r =>
                  (r' -> r') -> m r -> m r)
    -> (r' -> r')
    -> FreeT c m a
    -> FreeT c m a
liftLocal ask_ local_ f m =
    FreeT $
    \c -> do
        r <- ask_
        local_ f (runFreeT m (local_ (const r) . c))

instance (MonadIO m) => MonadIO (FreeT r m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}
