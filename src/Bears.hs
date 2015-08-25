{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# OPTIONS_GHC -fno-warn-orphans         #-}

{-| Example usage:

>>> let xs = fromList [(0, "Gabriel"), (1, "Oscar"), (2, "Edgar")] :: GroupBy Int Maybe String
>>> let ys = fromList [(0, "GabrielG439"), (1, "posco"), (3, "avibryant")] :: GroupBy Int Maybe String

    Inner join:

>>> toList ((,) <$> xs <*> ys)
Just [(0,("Gabriel","GabrielG439")),(1,("Oscar","posco"))]

    Left join:

>>> toList ((,) <$> xs <*> optional ys)
Just [(0,("Gabriel",Just "GabrielG439")),(1,("Oscar",Just "posco")),(2,("Edgar",Nothing))]

    Right join:

>>> toList ((,) <$> optional xs <*> ys)
Just [(0,(Just "Gabriel","GabrielG439")),(1,(Just "Oscar","posco")),(3,(Nothing,"avibryant"))]

    Indexing:

>>> lookup 0 xs
Just "Gabriel"
>>> lookup 0 ((,) <$> xs <*> ys)
Just ("Gabriel","GabrielG439")

    Choice:

>>> toList (xs <|> ys)
Just [(0,"Gabriel"),(1,"Oscar"),(2,"Edgar"),(3,"avibryant")]

    Concatenation (note the new types for @xs@ and @ys@):

>>> let xs = fromList [(0, "Gabriel"), (1, "Oscar"), (2, "Edgar")] :: GroupBy Int [] String
>>> let ys = fromList [(0, "GabrielG439"), (1, "posco"), (3, "avibryant")] :: GroupBy Int [] String
>>> toList (xs <|> ys)
Just [(0,"Gabriel"),(0,"GabrielG439"),(1,"Oscar"),(1,"posco"),(2,"Edgar"),(3,"avibryant")]

    Intermediate data sets are generated lazily, even if they are infinite:

>>> let ns = fromList [ (x, x) | x <- [0..] ] :: GroupBy Int Maybe Int
>>> lookup 2 ns
Just 2
>>> lookup 2 ((,) <$> ns <*> ns)
Just (2,2)
>>> lookup 2 (filter odd ns)
Nothing

-}

module Bears (
    -- * GroupBy
      GroupBy
    , Single

    -- * Construction
    , fromList
    , fromMap

    -- * Transformation
    , insert
    , filter
    , gt
    , ge
    , lt
    , le
    , fold
    , scan
    , optional

    -- * Elimination
    , lookup
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

{-| A data set where values are grouped by keys

    Think of this as conceptually associating each key with a collection of
    values:

> GroupBy k f v  ~  [(k, f v)]

    * @k@: the type of the key

    * @f@: the number of values in each group

    * @v@: the type of the value
-}
data GroupBy k f v = GroupBy
    { _keys :: Keys k
    , _lookup :: k -> f v 
    }

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
    { _keys   = Some (Set.fromList (fmap fst kvs))
    , _lookup = \k -> foldr cons empty [ fv | (k', fv) <- kvs, k == k' ]
    }
  where
    cons a as = pure a <|> as

-- | Convert a `Map` to a `GroupBy`
fromMap :: (Ord k, Alternative f) => Map k v -> GroupBy k f v
fromMap m = GroupBy
    { _keys   = Some (Set.fromList (Map.keys m))
    , _lookup = \k -> case Map.lookup k m of
        Nothing -> empty
        Just v  -> pure v
    }

{-| Insert a key-value pair

>>> let xs = fromList [('A', 1)] :: GroupBy Char [] Int
>>> toList (insert 'B' 2 xs)
Just [('A',1),('B',2)]

    For bulk updates you should instead use `fromList` and `(<|>)`

>>> toList (fromList [('B', 2), ('C', 3)] <|> xs)
Just [('A',1),('B',2),('C',3)]
-}
insert :: (Ord k, Alternative f) => k -> v -> GroupBy k f v -> GroupBy k f v
insert k v g = fromList [(k, v)] <|> g

-- | Only keep values that satisfy the given predicate
filter :: MonadPlus f => (v -> Bool) -> GroupBy k f v -> GroupBy k f v
filter predicate (GroupBy s f) = GroupBy s f'
  where
    f' = fmap (_filter predicate) f

_filter :: MonadPlus f => (v -> Bool) -> f v -> f v
_filter predicate vs = do
    v <- vs
    if predicate v then return v else mzero

-- | Filter out all groups whose key is greater than the given key
gt :: (Ord k, Alternative f) => k -> GroupBy k f v -> GroupBy k f v
gt k (GroupBy (Some s0) f) = GroupBy (Some s1) f'
  where
    (_, _, s1) = Set.splitMember k s0

    f' k' = if k < k' then f k' else empty
gt k (GroupBy (All  g ) f) = GroupBy (All  g') f'
  where
    g' k' = k < k' && g k
    f' k' = if k < k' then f k' else empty

-- | Filter out all groups whose key is greater than or equal to the given key
ge :: (Ord k, Alternative f) => k -> GroupBy k f v -> GroupBy k f v
ge k (GroupBy (Some s0) f) = GroupBy (Some s2) f'
  where
    (_, b, s1) = Set.splitMember k s0
    s2 = if b then Set.insert k s1 else s1

    f' k' = if k <= k' then f k' else empty
ge k (GroupBy (All  g ) f) = GroupBy (All  g') f'
  where
    g' k' = k <= k' && g k
    f' k' = if k <= k' then f k' else empty

-- | Filter out all groups whose key is less than the given key
lt :: (Ord k, Alternative f) => k -> GroupBy k f v -> GroupBy k f v
lt k (GroupBy (Some s0) f) = GroupBy (Some s1) f'
  where
    (s1, _, _) = Set.splitMember k s0

    f' k' = if k' < k then f k' else empty
lt k (GroupBy (All  g ) f) = GroupBy (All  g') f'
  where
    g' k' = k' < k && g k
    f' k' = if k' < k then f k' else empty

-- | Filter out all groups whose key is less than or equal to the given key
le :: (Ord k, Alternative f) => k -> GroupBy k f v -> GroupBy k f v
le k (GroupBy (Some s0) f) = GroupBy (Some s2) f'
  where
    (s1, b, _) = Set.splitMember k s0
    s2 = if b then Set.insert k s1 else s1

    f' k' = if k' <= k then f k' else empty
le k (GroupBy (All  g ) f) = GroupBy (All  g') f'
  where
    g' k' = k' <= k && g k
    f' k' = if k' <= k then f k' else empty

{-| Reduce each group to a `Single` value

>>> import qualified Control.Foldl as Fold
>>> let xs = fromList [('A', 1), ('A', 2), ('A', 3), ('B', 4), ('B', 5), ('C', 6)] :: GroupBy Char [] Int
>>> toList (fold Fold.sum xs)
Just [('A',6),('B',9),('C',6)]
>>> toList (fold Fold.length xs)
Just [('A',3),('B',2),('C',1)]
>>> toList (fold Fold.list xs)
Just [('A',[1,2,3]),('B',[4,5]),('C',[6])]
-}
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

-- | Find all values that match the given key
lookup :: k -> GroupBy k f v -> f v
lookup k g = _lookup g k

{-| Convert a `GroupBy` to a list

    Returns `Nothing` if the `GroupBy` represents a function instead of a `Set`
-}
toList :: Foldable f => GroupBy k f v -> Maybe [(k, v)]
toList (GroupBy (Some s) f) =
    Just [ (k, v) | k <- Set.toList s, v <- Foldable.toList (f k) ]
toList  _                   =
    Nothing
