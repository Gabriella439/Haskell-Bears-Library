{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# OPTIONS_GHC -fno-warn-orphans         #-}

{-| This library provides a simple and reasonably efficient Haskell implementation
    of relational operations on in-memory `Table`s

    Example usage:

>>> let xs = fromList [(0, "Gabriel"), (1, "Oscar"), (2, "Edgar")]
>>> let ys = fromList [(0, "GabrielG439"), (1, "posco"), (3, "avibryant")]

    Inner join:

>>> :set -XApplicativeDo
>>> do x <- xs; y <- ys; return (x, y)
Table {rows = fromList [(0,("Gabriel","GabrielG439")),(1,("Oscar","posco"))], fallback = Nothing}

    Left join:

>>> do x <- xs; y <- optional ys; return (x, y)
Table {rows = fromList [(0,("Gabriel",Just "GabrielG439")),(1,("Oscar",Just "posco")),(2,("Edgar",Nothing))], fallback = Nothing}

    Right join:

>>> do x <- optional xs; y <- ys; return (x, y)
Table {rows = fromList [(0,(Just "Gabriel","GabrielG439")),(1,(Just "Oscar","posco")),(3,(Nothing,"avibryant"))], fallback = Nothing}

    Outer join:

>>> do x <- optional xs; y <- optional ys; return (x, y)
Table {rows = fromList [(0,(Just "Gabriel",Just "GabrielG439")),(1,(Just "Oscar",Just "posco")),(2,(Just "Edgar",Nothing)),(3,(Nothing,Just "avibryant"))], fallback = Just (Nothing,Nothing)}

    Indexing:

>>> lookup 0 xs
Just "Gabriel"
>>> lookup 0 (do x <- xs; y <- ys; return (x, y))
Just ("Gabriel","GabrielG439")

    Choice:

>>> xs <|> ys
Table {rows = fromList [(0,"Gabriel"),(1,"Oscar"),(2,"Edgar"),(3,"avibryant")], fallback = Nothing}

-}

module Bears (
    -- * Table
      Table(..)
    , singleton
    , fromList
    , insert
    , lookup
    , gt
    , ge
    , lt
    , le
    , filter
    , take

    -- * Groups
    , Groups(..)
    , groupBy
    , fold

#if MIN_VERSION_foldl(1,2,2)
    -- * Description
    , Description(..)
    , describe
#endif

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

    -- * CSV
    , Csv.HasHeader(..)
    , readCsv
    , readNamedCsv
    , writeCsv
    , writeNamedCsv

    -- * Re-exports
    , module Bears.TH
    , optional
    ) where

import Bears.TH
import Control.Applicative
import Control.Exception (throwIO)
import Control.Foldl (Fold(..))
import Control.Monad (MonadPlus(..), join, mfilter)
import Control.Monad.Trans.State (state, evalState)
import Data.ByteString.Lazy (ByteString)
import Data.Map (Map)
import Data.Monoid ((<>))
import Data.Set (Set)
import Data.Vector (Vector)
import Prelude hiding (filter, lookup, take)

import qualified Control.Foldl
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Csv             as Csv
import qualified Data.Foldable
import qualified Data.List
import qualified Data.Map.Strict
import qualified Data.Sequence
import qualified Data.Vector

-- | Efficiently deserialize CSV records
readCsv
    :: Csv.FromRecord a
    => Csv.HasHeader
    -- ^ Data contains header that should be skipped
    -> FilePath
    -- ^ Path to CSV file
    -> IO (Vector a)
readCsv hasHeader path = do
    bytes <- ByteString.readFile path
    case Csv.decode hasHeader bytes of
        Left str -> throwIO (userError str)
        Right as -> return as

-- | Efficiently deserialize CSV records.  The data must be preceded by a header
readNamedCsv
    :: Csv.FromNamedRecord a
    => FilePath
    -- ^ Path to CSV file
    -> IO (Csv.Header, Vector a)
readNamedCsv path = do
    bytes <- ByteString.readFile path
    case Csv.decodeByName bytes of
        Left   str         -> throwIO (userError str)
        Right (header, as) -> return (header, as)

-- | Efficiently serialize CSV records
writeCsv :: Csv.ToRecord a => FilePath -> Vector a -> IO ()
writeCsv path as = ByteString.writeFile path (Csv.encode (Data.Foldable.toList as))

{-| Efficiently serialize CSV records.  The header is written before any records
    and dictates the field order.
-}
writeNamedCsv
    :: Csv.ToNamedRecord a => FilePath -> Csv.Header -> Vector a -> IO ()
writeNamedCsv path header as =
    ByteString.writeFile path (Csv.encodeByName header (Data.Foldable.toList as))

{-| A `Table` is an in-memory datatype analogous to a database table supporting
    functionality similar to SQL operations, with one difference: a `Table` can
    optionally supply a `fallback` result if queried for a missing key

    The type parameters of `Table` are:

    * @k@: the type of primary key of the `Table`
    * @v@: the type of each row of the `Table` (not including the primary key)

    You can create a `Table` using:

    * `singleton`
    * `fromList`
    * `empty`
    * `pure`
    * the `Table` constructor

    You can transform a `Table` using:

    * `insert`
    * `filter`
    * `fmap`
    * `traverse`
    * `gt` \/ `lt` \/ `ge` \/ `le`

    You can combine `Table`s using:

    * (`<|>`)
    * `Applicative` operations, including @ApplicativeDo@

    You can consume `Table`s using:

    * `lookup`
    * `Foldable` operations, including `toList`
    * pattern matching on the `Table` constructor
-}
data Table k v = Table
    { rows     :: Map k v
    , fallback :: Maybe v
    } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Ord k => Applicative (Table k) where
    pure v = Table Data.Map.Strict.empty (pure v)

    Table lm (Just lv) <*> Table rm (Just rv) = Table m (pure (lv rv))
      where
        m = Data.Map.Strict.unions [apply lm rm, fmap lv rm, fmap ($ rv) lm]
    Table lm Nothing <*> Table rm (Just rv) = Table m empty
      where
        m = Data.Map.Strict.union (apply lm rm) (fmap ($ rv) lm)
    Table lm (Just lv) <*> Table rm Nothing  = Table m empty
      where
        m = Data.Map.Strict.union (apply lm rm) (fmap lv rm)
    Table lm Nothing <*> Table rm Nothing = Table m empty
      where
        m = apply lm rm

instance Ord k => Alternative (Table k) where
    empty = Table Data.Map.Strict.empty empty

    Table lm lv <|> Table rm rv = Table (Data.Map.Strict.union lm rm) (lv <|> rv)

apply :: Ord k => Map k (a -> b) -> Map k a -> Map k b
apply lm rm = Data.Map.Strict.mergeWithKey
    (\_ a b -> Just (a b))
    (\_ -> Data.Map.Strict.empty)
    (\_ -> Data.Map.Strict.empty)
    lm
    rm

{-| Insert a key-value pair

> insert k v t = singleton k v <|> t

>>> let t = fromList [('A', 1)]
>>> insert 'B' 2 t
Table {rows = fromList [('A',1),('B',2)], fallback = Nothing}

    For bulk updates you should instead use `fromList` and (`<|>`)

>>> fromList [('B', 2), ('C', 3)] <|> t
Table {rows = fromList [('A',1),('B',2),('C',3)], fallback = Nothing}
-}
insert :: Ord k => k -> v -> Table k v -> Table k v
insert k v t = singleton k v <|> t

-- | Create a `Table` from a single key-value pair
singleton :: k -> v -> Table k v
singleton k v = Table (Data.Map.Strict.singleton k v) empty

-- | Create a `Table` from a list of key-value pairs
fromList :: Ord k => [(k, v)] -> Table k v
fromList kvs = Table (Data.Map.Strict.fromList kvs) empty

{-| Retrieve a row from a `Table` by the primary key

>>> import qualified Data.Map as Map
>>> let t = Table { rows = Map.fromList [(0,"Gabriel"),(1,"Oscar"),(2,"Edgar")], fallback = Nothing }
>>> lookup 0 t
Just "Gabriel"
>>> lookup 1 t
Just "Oscar"
>>> lookup 3 t
Nothing

    If the `Table` supplies a `fallback` then `lookup` will return that value if no
    row matches the given key:

>>> let t = Table { rows = Map.fromList [(0,"Gabriel"),(1,"Oscar"),(2,"Edgar")], fallback = Just "John" }
>>> lookup 3 t
Just "John"

-}
lookup :: Ord k => k -> Table k v -> Maybe v
lookup k (Table m v) = Data.Map.Strict.lookup k m <|> v

{-| Analogous to a @GROUP BY@ SQL clause

    The type parameters of `Groups` are:

    * @k@: the type of primary key associated with each group
    * @v@: the element type stored within each group

    You can create a `Group` using:

    * `groupBy` / `group`
    * `pure`

    You can transform a `Group` using:

    * `fmap`
    * `traverse`

    You can combine `Group`s using:

    * (`<|>`)
    * `Applicative` operations (including @ApplicativeDo@)

    You can consume `Group`s using:

    * `fold`
    * pattern matching on the `Groups` constructor
-}
newtype Groups k v = Groups { toTable :: Table k (Vector v) }
    deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Ord k => Applicative (Groups k) where
    pure x = Groups (pure (pure x))

    Groups l <*> Groups r = Groups (liftA2 (<*>) l r)

instance Ord k => Alternative (Groups k) where
    empty = Groups (pure empty)

    Groups l <|> Groups r = Groups (liftA2 (<|>) l r)

{-| This function is analogous to a @GROUP BY@ clause in an SQL expression

    Note that `Table`s are `Foldable`, so you can use `groupBy` on a `Table`:

> groupBy :: (v -> k) -> Table k' v -> Groups k v

    ... but you can also use `groupBy` on a list or `Vector`, too:

> groupBy :: (v -> k) ->       [v] -> Groups k v
> groupBy :: (v -> k) -> Vector v  -> Groups k v

>>> let kvs = [('A', 1), ('A', 2), ('A', 3), ('B', 4), ('B', 5), ('C', 6)]
>>> fmap snd (groupBy fst kvs)
Groups {toTable = Table {rows = fromList [('A',[1,2,3]),('B',[4,5]),('C',[6])], fallback = Nothing}}
-}
groupBy :: (Foldable f, Ord k) => (v -> k) -> f v -> Groups k v
groupBy key vs = Groups (Table m Nothing)
  where
    kvs = do
        v <- Data.Foldable.toList vs
        return (key v, Data.Sequence.singleton v)

    toVector = Data.Vector.fromList . Data.Foldable.toList

    m = fmap toVector (Data.Map.Strict.fromListWith (flip (<>)) kvs)

{-| Analogous to an SQL aggregate function

    For example:

    * the analog of @COUNT(*)@   is @fold Control.Foldl.length@
    * the analog of @AVERAGE(*)@ is @fold Control.Foldl.mean@
    * the analog of @MAXIMUM(*)@ is @fold Control.Foldl.maximum@
    * the analog of @MINIMUM(*)@ is @fold Control.Foldl.minimum@
    * the analog of @SUM(*)@     is @fold Control.Foldl.sum@

    You can also fold on a specific column by using `lmap`.  For example, given this
    datatype definition for a row:

    > data Row = Row { bar :: Int, baz :: Bool }

    ... then the analog of @COUNT(bar)@ is @fold (lmap bar Control.Foldl.length)@

    `fold` reduces each group to a single value using the supplied `Fold`

>>> import qualified Control.Foldl as Fold
>>> let kvs = [('A', 1), ('A', 2), ('A', 3), ('B', 4), ('B', 5), ('C', 6)]
>>> let gs = fmap snd (groupBy fst kvs)
>>> fold Fold.sum gs
Table {rows = fromList [('A',6),('B',9),('C',6)], fallback = Nothing}
>>> fold Fold.length gs
Table {rows = fromList [('A',3),('B',2),('C',1)], fallback = Nothing}
>>> fold Fold.list gs
Table {rows = fromList [('A',[1,2,3]),('B',[4,5]),('C',[6])], fallback = Nothing}
-}
fold :: Fold v r -> Groups k v -> Table k r
fold f (Groups g) = fmap (Control.Foldl.fold f) g

#if MIN_VERSION_foldl(1,2,2)
-- | This is the record type for the output of `describe`
data Description a = Description
    { _count :: Int
    , _mean  :: a
    , _std   :: a
    , _min   :: Maybe a
    , _max   :: Maybe a
    } deriving (Show)

{-| Analogous to the @.describe()@ method from @pandas@

>>> Control.Foldl.fold describe [0..10]
Description {_count = 11, _mean = 5.0, _std = 3.1622776601683795, _min = Just 0.0, _max = Just 10.0}

    Note that this works on any type that implements `Floating` and `Ord`, including
    types like `R3`.  You can also generate a `Floating` instance for any
    polymorphic record type using `deriveRow`

>>> Control.Foldl.fold describe [R3 1 2 3, R3 4 5 6, R3 7 8 9]
Description {_count = 3, _mean = R3 4.0 5.0 6.0, _std = R3 2.449489742783178 2.449489742783178 2.449489742783178, _min = Just (R3 1.0 2.0 3.0), _max = Just (R3 7.0 8.0 9.0)}

-}
describe :: (Floating a, Ord a) => Fold a (Description a)
describe = do
    _count <- Control.Foldl.length
    _mean  <- Control.Foldl.mean
    _std   <- Control.Foldl.std
    _min   <- Control.Foldl.minimum
    _max   <- Control.Foldl.maximum
    return (Description {..})
#endif

{-| Analogous to a @WHERE@ SQL clause

    Only keep values that satisfy the given predicate
-}
filter :: (v -> Bool) -> Table k v -> Table k v
filter predicate (Table m v) = Table m' v'
  where
    m' = Data.Map.Strict.filter predicate m

    v' = mfilter predicate v

{-| Analogous to a @LIMIT@ SQL clause

    Retrieve up to the specified number of values

>>> let t = fromList (zip [0..] ["Test", "ABC", "Foo", "Dog"])
>>> t
Table {rows = fromList [(0,"Test"),(1,"ABC"),(2,"Foo"),(3,"Dog")], fallback = Nothing}
>>> take 2 t
Table {rows = fromList [(0,"Test"),(1,"ABC")], fallback = Nothing}
-}
take :: Eq k => Int -> Table k v -> Table k v
take n (Table m v) = Table (adapt m) v
  where
    adapt =
          Data.Map.Strict.fromDistinctAscList
        . Data.List.take n
        . Data.Map.Strict.toAscList

-- | Filter out all groups whose key is greater than the given key
gt :: Ord k => k -> Table k v -> Table k v
gt k (Table m v) = Table m' v
  where
    (_, m')  = Data.Map.Strict.split k m

-- | Filter out all groups whose key is greater than or equal to the given key
ge :: Ord k => k -> Table k v -> Table k v
ge k (Table m v) = Table m'' v
  where
    (_, mv, m') = Data.Map.Strict.splitLookup k m

    m'' = case mv of
        Nothing ->                             m'
        Just v' -> Data.Map.Strict.insert k v' m'

-- | Filter out all groups whose key is less than the given key
lt :: Ord k => k -> Table k v -> Table k v
lt k (Table m v) = Table m' v
  where
    (m', _) = Data.Map.Strict.split k m

-- | Filter out all groups whose key is less than or equal to the given key
le :: Ord k => k -> Table k v -> Table k v
le k (Table m v) = Table m'' v
  where
    (m', mv, _) = Data.Map.Strict.splitLookup k m

    m'' = case mv of
        Nothing ->                             m'
        Just v' -> Data.Map.Strict.insert k v' m'

-- | A polymorphic record with 0 fields that implements numeric type classes
data R0 = R0 deriving (Eq, Ord, Show)

deriveRow ''R0

-- | Transpose an `R0` record
transposeR0 :: Applicative f => R0 -> f R0

-- | A polymorphic record with 1 field that implements numeric type classes
data R1 a = R1 !a deriving (Eq, Ord, Show)

deriveRow ''R1

-- | Transpose an `R1` record
transposeR1 :: Applicative f => R1 (f a) -> f (R1 a)

-- | A polymorphic record with 2 fields that implements numeric type classes
data R2 a b = R2 !a !b deriving (Eq, Ord, Show)

deriveRow ''R2

-- | Transpose an `R2` record
transposeR2 :: Applicative f => R2 (f a) (f b) -> f (R2 a b)

-- | A polymorphic record with 3 fields that implements numeric type classes
data R3 a b c = R3 !a !b !c deriving (Eq, Ord, Show)

deriveRow ''R3

-- | Transpose an `R3` record
transposeR3 :: Applicative f => R3 (f a) (f b) (f c) -> f (R3 a b c)

-- | A polymorphic record with 4 fields that implements numeric type classes
data R4 a b c d = R4 !a !b !c !d deriving (Eq, Ord, Show)

deriveRow ''R4

-- | Transpose an `R4` record
transposeR4 :: Applicative f => R4 (f a) (f b) (f c) (f d) -> f (R4 a b c d)
