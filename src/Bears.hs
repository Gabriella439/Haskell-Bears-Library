{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# OPTIONS_GHC -fno-warn-orphans         #-}

module Bears (
    -- * GroupBy
      GroupBy
    , Single

    -- * Construction
    , fromList
    , fromMap

    -- * Transformation
    , filter
    , fold
    , scan

    -- * Elimination
    , toList
    ) where

import Control.Applicative
import Control.Foldl (Fold(..))
import Control.Monad (MonadPlus(..))
import Control.Monad.Trans.State (state, evalState)
import Data.Map (Map)
import Data.Set (Set)
import Prelude hiding (filter, lookup)

import qualified Control.Foldl           as Fold
import qualified Data.Foldable           as Foldable
import qualified Data.Map                as Map
import qualified Data.Set                as Set

instance Num Bool where
    fromInteger 0         = False
    fromInteger n | n > 0 = True

    (+) = (||)
    (*) = (&&)

instance Num b => Num (a -> b) where
    fromInteger n = pure (fromInteger n)

    negate = fmap negate
    abs    = fmap abs
    signum = fmap signum

    (+) = liftA2 (+)
    (*) = liftA2 (*)

data Keys k = All (k -> Bool) | Some (Set k)

instance Ord k => Num (Keys k) where
    fromInteger 0         = Some Set.empty
    fromInteger n | n > 0 = All 1

    All  x + All  y = All  (                x +                 y)
    Some x + All  y = All  (flip Set.member x +                 y)
    All  x + Some y = All  (                x + flip Set.member y)
    Some x + Some y = Some (Set.union x y)

    All  x * All  y = All  (x * y)
    All  x * Some y = Some (Set.filter x y)
    Some x * All  y = Some (Set.filter y x)
    Some x * Some y = Some (Set.intersection x y)

-- | A collection that holds a `Single` value
newtype Single a = Single a deriving (Functor, Foldable, Traversable, Show)

instance Applicative Single where
    pure = Single

    Single f <*> Single x = Single (f x)

{-| A data set grouped by some key

    Think of this as conceptually:

> GroupBy k f v  ~  [(k, f v)]

    * @k@: the type of the key

    * @f@: the number of values in each group

    * @v@: the type of the value
-}
data GroupBy k f v = GroupBy { keys :: Keys k, lookup :: k -> f v }

instance Functor f => Functor (GroupBy k f) where
    fmap f (GroupBy s k) = GroupBy s (fmap (fmap f) k)

instance (Ord k, Applicative f) => Applicative (GroupBy k f) where
    pure v = GroupBy 1 (pure (pure v))

    GroupBy s1 f1 <*> GroupBy s2 f2 = GroupBy (s1 * s2) (liftA2 (<*>) f1 f2)

instance (Ord k, Alternative f) => Alternative (GroupBy k f) where
    empty = GroupBy 0 (pure empty)

    GroupBy s1 f1 <|> GroupBy s2 f2 = GroupBy (s1 + s2) (liftA2 (<|>) f1 f2)

-- | Convert a list to a `GroupBy`
fromList :: (Ord k, Alternative f) => [(k, v)] -> GroupBy k f v
fromList kvs = GroupBy
    { keys   = Some (Set.fromList (fmap fst kvs))
    , lookup = \k -> foldr cons empty [ fv | (k', fv) <- kvs, k == k' ]
    }
  where
    cons a as = pure a <|> as

-- | Convert a `Map` to a `GroupBy`
fromMap :: (Ord k, Alternative f) => Map k v -> GroupBy k f v
fromMap m = GroupBy
    { keys   = Some (Set.fromList (Map.keys m))
    , lookup = \k -> case Map.lookup k m of
        Nothing -> empty
        Just v  -> pure v
    }

-- | Only keep values that satisfy the given predicate
filter :: MonadPlus f => (v -> Bool) -> GroupBy k f v -> GroupBy k f v
filter predicate (GroupBy s f) = GroupBy s f'
  where
    f' = fmap (_filter predicate) f

_filter :: MonadPlus f => (v -> Bool) -> f v -> f v
_filter predicate vs = do
    v <- vs
    if predicate v then return v else mzero

-- | Reduce each group to a `Single` value
fold :: Foldable f => Fold v r -> GroupBy k f v -> GroupBy k Single r
fold fvr (GroupBy s f) = GroupBy s f'
  where
    f' = fmap (Single . Fold.fold fvr) f

-- | Transform each element of a group using scan derived from a `Fold`
scan :: Traversable f => Fold a b -> GroupBy k f a -> GroupBy k f b
scan fab (GroupBy s f) = GroupBy s f'
  where
    f' = fmap (_scan fab) f

-- This belongs upstream in `foldl`
_scan :: Traversable f => Fold a b -> f a -> f b
_scan (Fold step begin done) as =
    evalState (traverse (\a -> state (\x -> let y = step x a in (done y, y))) as) begin

{-| Convert a `GroupBy` to a list

    Returns `Nothing` if the `GroupBy` represents a function instead of a `Set`
-}
toList :: Foldable f => GroupBy k f v -> Maybe [(k, v)]
toList (GroupBy (Some s) f) =
    Just [ (k, v) | k <- Set.toList s, v <- Foldable.toList (f k) ]
toList  _                   =
    Nothing
