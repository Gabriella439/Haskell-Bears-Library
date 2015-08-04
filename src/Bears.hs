{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-|
>>> :set -XOverloadedLists
-}

module Bears (
      module Bears
    , encode
    , decode
    ) where

import Control.Applicative
import Control.Exception (throwIO)
import Control.Foldl (Fold(..))
import Data.Csv (FromRecord, HasHeader(..), ToRecord, decode, encode)
import Data.Functor.Constant (Constant(..))
import Data.Hashable (Hashable)
import Data.List (foldl')
import Data.Map.Strict (Map)
import Data.Monoid (Sum(..))
import Data.Set (Set)
import Data.Vector (Vector)
import Lens.Family.Stock
import GHC.Exts (IsList(..))
import Prelude hiding (group, length, lookup, sum)

import qualified Control.Foldl           as Fold
import qualified Data.ByteString.Lazy    as ByteString
import qualified Data.Foldable           as Foldable
import qualified Data.HashMap.Strict     as HashMap
import qualified Data.Set                as Set
import qualified Data.Vector             as Vector
import qualified Network.HTTP.Client     as HTTP
import qualified Network.HTTP.Client.TLS as HTTP

data Keys k = All | Some (Set k)

instance Ord k => Num (Keys k) where
    fromInteger 0         = Some Set.empty
    fromInteger n | n > 0 = All

    All     + _       = All
    _       + All     = All
    Some s1 + Some s2 = Some (Set.union s1 s2)

    All     * ks      = ks
    ks      * All     = ks
    Some s1 * Some s2 = Some (Set.intersection s1 s2)

data Indexed k v = Indexed { keys :: Keys k, lookup :: k -> Maybe [v] }

instance (Show k, Show v) => Show (Indexed k v) where
    show i = case scatter i of
        Just u -> "group " ++ show u

instance Functor (Indexed k) where
    fmap f (Indexed s k) = Indexed s (fmap (fmap (fmap f)) k)

instance Ord k => Applicative (Indexed k) where
    pure v = Indexed 1 (pure (pure (pure v)))

    Indexed s1 f1 <*> Indexed s2 f2 = Indexed (s1 * s2) (liftA2 (liftA2 (<*>)) f1 f2)

instance Ord k => Alternative (Indexed k) where
    empty = Indexed 0 (pure empty)

    Indexed s1 f1 <|> Indexed s2 f2 = Indexed (s1 + s2) (liftA2 (<|>) f1 f2)

group :: (Ord k, Hashable k) => Vector (k, v) -> Indexed k v
group kvs = Indexed
    { keys   = Some (Set.fromList (Vector.toList (Vector.map fst kvs)))
    , lookup = \k -> HashMap.lookup k m
    }
  where
    m = HashMap.fromListWith (++) (map (\(k, v) -> (k, [v])) (Vector.toList kvs))

scatter :: Indexed k v -> Maybe (Vector (k, v))
scatter (Indexed (Some s) f) =
    Just (Vector.fromList [ (k, v) | k <- Set.toList s, Just vs <- [f k], v <- vs ])
scatter  _                   = Nothing

{-|
>>> aggregate sum [(1,1),(2,2),(1,3)]
[(1,4),(2,2)]
-}
aggregate
    :: (Eq k, Hashable k) => Fold v r -> Vector (k, v) -> Vector (k, r)
aggregate (Fold step begin done) kvs = 
    Vector.fromList
        (HashMap.toList (fmap done (Vector.foldl' step' HashMap.empty kvs)))
  where
    step' m (k, v) = case HashMap.lookup k m of
        Nothing -> HashMap.insert k (step begin v) m
        Just x  -> HashMap.insert k (step x     v) m

fold :: Fold a b -> Vector a -> b
fold = Fold.fold 

scan :: Fold a b -> Vector a -> Vector b
scan (Fold step begin done) as = Vector.map done (Vector.scanl' step begin as)
