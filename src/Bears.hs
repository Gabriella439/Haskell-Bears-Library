{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
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
    -- * CSV
      Csv.HasHeader(..)
    , readCsv
    , readNamedCsv
    , writeCsv
    , writeNamedCsv

    -- * GroupBy
    , GroupBy(..)
    , Keys(..)
    , Single(..)

    -- * Construction
    , fromList
    , fromMap

    -- * Transformation
    , insert
    , fold
    , scan
    , flatten
    , filter
    , gt
    , ge
    , lt
    , le
    , eq
    , optional
    , take

    -- * Elimination
    , lookup
    , toList
    , toMap

    -- * Records
    , R0(..)
    , transposeR0
    , R1(..)
    , transposeR1
    , R2(..)
    , transposeR2
    , R3(..)
    , transposeR3
    , R4(..)
    , transposeR4

    -- * Re-exports
    , module Bears.TH
    , view
    , over
    ) where

import Bears.TH
import Control.Applicative
import Control.Exception (throwIO)
import Control.Foldl (Fold(..))
import Control.Lens (Field1(..), Field2(..), Field3(..), Field4(..), view, over)
import Control.Monad (MonadPlus(..), join)
import Control.Monad.Trans.State (state, evalState)
import Data.ByteString.Lazy (ByteString)
import Data.Map (Map)
import Data.Set (Set)
import Prelude hiding (filter, lookup)

import qualified Control.Foldl        as Fold
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Csv             as Csv
import qualified Data.Foldable        as Foldable
import qualified Data.List
import qualified Data.Map             as Map
import qualified Data.Set             as Set

-- | Efficiently deserialize CSV records
readCsv
    :: Csv.FromRecord a
    => Csv.HasHeader
    -- ^ Data contains header that should be skipped
    -> FilePath
    -- ^ Path to CSV file
    -> IO [a]
readCsv hasHeader path = do
    bytes <- ByteString.readFile path
    case Csv.decode hasHeader bytes of
        Left str -> throwIO (userError str)
        Right as -> return (Foldable.toList as)

-- | Efficiently deserialize CSV records.  The data must be preceded by a header
readNamedCsv
    :: Csv.FromNamedRecord a
    => FilePath
    -- ^ Path to CSV file
    -> IO (Csv.Header, [a])
readNamedCsv path = do
    bytes <- ByteString.readFile path
    case Csv.decodeByName bytes of
        Left   str         -> throwIO (userError str)
        Right (header, as) -> return (header, Foldable.toList as)

-- | Efficiently serialize CSV records
writeCsv :: Csv.ToRecord a => FilePath -> [a] -> IO ()
writeCsv path as = ByteString.writeFile path (Csv.encode as)

{-| Efficiently serialize CSV records.  The header is written before any records
    and dictates the field order.
-}
writeNamedCsv :: Csv.ToNamedRecord a => FilePath -> Csv.Header -> [a] -> IO ()
writeNamedCsv path header as =
    ByteString.writeFile path (Csv.encodeByName header as)

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

instance Foldable f => Foldable (GroupBy k f) where
    foldMap _ (GroupBy (All  _   ) _) = mempty
    foldMap f (GroupBy (Some keys) k) = foldMap (foldMap f . k) keys

-- | Convert a list to a `GroupBy`
fromList :: (Ord k, Alternative f) => [(k, v)] -> GroupBy k f v
fromList kvs = GroupBy
    { _keys   = Some (Set.fromList (fmap fst kvs))
    , _lookup = \k ->
        let cons (k', v) vs = if k == k' then pure v <|> vs else vs
        in  foldr cons empty kvs
    }

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

    For bulk updates you should instead use `fromList` and (`<|>`)

>>> toList (fromList [('B', 2), ('C', 3)] <|> xs)
Just [('A',1),('B',2),('C',3)]
-}
insert :: (Ord k, Alternative f) => k -> v -> GroupBy k f v -> GroupBy k f v
insert k v g = fromList [(k, v)] <|> g

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

{-| If each value is a collection of the same type as the surrounding group,
    flatten the two collections

>>> let xs = fromList [('A', [0, 1]), ('B', [2, 3])] :: GroupBy Char [] [Int]
>>> toList (flatten xs)
Just [('A',0),('A',1),('B',2),('B',3)]
-}
flatten :: Monad f => GroupBy k f (f v) -> GroupBy k f v
flatten (GroupBy s f) = GroupBy s (fmap join f)

{-| Sort each group

>>> let xs = fromList [('A', 2), ('A', 1), ('B', 4), ('B', 3)]
>>> toList (sort xs)
Just [('A',1),('A',2),('B',3),('B',4)]
-}
sort :: Ord v => GroupBy k [] v -> GroupBy k [] v
sort (GroupBy s f) = GroupBy s (fmap Data.List.sort f)

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

-- | Select just the groups whose key is exactly equal to the given key
eq :: (Ord k, Alternative f) => k -> GroupBy k f v -> GroupBy k f v
eq k (GroupBy s0 f) = GroupBy s1 f'
  where
    s1 = Some (Set.singleton k) * s0

    f' k' = if k == k' then f k else empty

-- | Find all values that match the given key
lookup :: k -> GroupBy k f v -> f v
lookup k g = _lookup g k

{-| Convert a `GroupBy` to a list

    Returns `Nothing` if the `GroupBy` represents a function instead of a `Set`
    keys
-}
toList :: Foldable f => GroupBy k f v -> Maybe [(k, v)]
toList (GroupBy (Some s) f) =
    Just [ (k, v) | k <- Set.toList s, v <- Foldable.toList (f k) ]
toList  _                   =
    Nothing

{-| Convert a `GroupBy` to a `Map`

    Returns `Nothing` if the `GroupBy` represents a function instead of a `Set`
    of keys
-}
toMap :: (Eq k, Foldable f) => GroupBy k f v -> Maybe (Map k v)
toMap = fmap Map.fromAscList . toList

data R0 = R0 deriving (Eq, Ord, Show)

deriveRow ''R0

data R1 a = R1 !a deriving (Eq, Ord, Show)

deriveRow ''R1

instance Field1 (R1 a) (R1 a') a a' where
    _1 k (R1 a) = fmap R1 (k a)

data R2 a b = R2 !a !b deriving (Eq, Ord, Show)

deriveRow ''R2

instance Field1 (R2 a b) (R2 a' b) a a' where
    _1 k (R2 a b) = fmap (\a' -> R2 a' b) (k a)

instance Field2 (R2 a b) (R2 a b') b b' where
    _2 k (R2 a b) = fmap (\b' -> R2 a b') (k b)

data R3 a b c = R3 !a !b !c deriving (Eq, Ord, Show)

deriveRow ''R3

instance Field1 (R3 a b c) (R3 a' b c) a a' where
    _1 k (R3 a b c) = fmap (\a' -> R3 a' b c) (k a)

instance Field2 (R3 a b c) (R3 a b' c) b b' where
    _2 k (R3 a b c) = fmap (\b' -> R3 a b' c) (k b)

instance Field3 (R3 a b c) (R3 a b c') c c' where
    _3 k (R3 a b c) = fmap (\c' -> R3 a b c') (k c)

data R4 a b c d = R4 !a !b !c !d deriving (Eq, Ord, Show)

deriveRow ''R4

instance Field1 (R4 a b c d) (R4 a' b c d) a a' where
    _1 k (R4 a b c d) = fmap (\a' -> R4 a' b c d) (k a)

instance Field2 (R4 a b c d) (R4 a b' c d) b b' where
    _2 k (R4 a b c d) = fmap (\b' -> R4 a b' c d) (k b)

instance Field3 (R4 a b c d) (R4 a b c' d) c c' where
    _3 k (R4 a b c d) = fmap (\c' -> R4 a b c' d) (k c)

instance Field4 (R4 a b c d) (R4 a b c d') d d' where
    _4 k (R4 a b c d) = fmap (\d' -> R4 a b c d') (k d)
