{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes                 #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-|
>>> :set -XOverloadedLists
-}

module Bears where

import Control.Applicative
import Data.List (foldl')
import Data.Functor.Constant (Constant(..))
import Data.Discrimination hiding (group)
import Data.Monoid (Sum(..))
import Data.Set (Set)
import Data.Map.Strict (Map)
import Lens.Family.Stock
import GHC.Exts (IsList(..))
import Prelude hiding (group, length, lookup, sum)

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

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

newtype Unindexed v = Unindexed { getUnindexed :: [v] }
    deriving (Functor, Applicative, Alternative)

instance Show v => Show (Unindexed v) where
    show = show . getUnindexed

instance IsList (Unindexed v) where
    type Item (Unindexed v) = v

    fromList = Unindexed

    toList = getUnindexed

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

data Pair a b = P !a !b

instance (Monoid a, Monoid b) => Monoid (Pair a b) where
    mempty = P mempty mempty

    mappend (P xL yL) (P xR yR) = P (mappend xL xR) (mappend yL yR)

data Aggregate a b = forall m . Monoid m => Aggregate (a -> m) (m -> b)

instance Functor (Aggregate a) where
     fmap f (Aggregate tally summarize) = Aggregate tally (f . summarize)

instance Applicative (Aggregate a) where
    pure b = Aggregate (\_ -> ()) (\_ -> b)

    Aggregate tallyL summarizeL <*> Aggregate tallyR summarizeR =
        Aggregate tally summarize
      where
        tally a = P (tallyL a) (tallyR a)

        summarize (P l r) = summarizeL l (summarizeR r)

group :: (Ord k, Sorting k) => Unindexed (k, v) -> Indexed k v
group (Unindexed kvs) = Indexed
    { keys   = Some (toSet (map fst kvs))
    , lookup = \k -> Map.lookup k m
    }
  where
    m = toMapWith (++) (map (\(k, v) -> (k, [v])) kvs)

scatter :: Indexed k v -> Maybe (Unindexed (k, v))
scatter (Indexed (Some s) f) =
    Just (Unindexed [ (k, v) | k <- Set.toList s, Just vs <- [f k], v <- vs ])
scatter  _                   = Nothing

{-|
>>> aggregate sum [(1,1),(2,2),(1,3)] :: Unindexed (Int, Int)
[(1,4),(2,2)]
-}
aggregate :: Sorting k => Aggregate v r -> Unindexed (k, v) -> Unindexed (k, r)
aggregate (Aggregate tally summarize) (Unindexed kvs) =
    Unindexed
        (Map.toList
            (fmap
                summarize
                (toMapWith mappend (map (\(k, v) -> (k, tally v)) kvs)) ))

{-|
>>> fold ((,) <$> sum <*> length) [0..10]
(55,11)
-}
fold :: Aggregate a b -> Unindexed a -> b
fold (Aggregate tally summarize) (Unindexed as) =
    summarize (foldl' mappend mempty (map tally as))

{-|
>>> scan sum [1,2,3]
[0,1,3,6]
-}
scan :: Aggregate a b -> Unindexed a -> Unindexed b
scan (Aggregate tally summarize) (Unindexed as) = Unindexed (foldr cons nil as mempty)
  where
    nil      x = summarize x:[]
    cons a k x = summarize x:(k $! mappend x (tally a))

type Handler a b = forall m . Monoid m => (b -> Constant m b) -> (a -> Constant m a)

{-|
>>> fold (handles _Just sum) [Nothing , Just 1, Nothing, Just 3]
4
>>> fold (handles _1 sum) [(1, "A"), (2, "B"), (3, "C")]
6
-}
handles :: Handler a b -> Aggregate b r -> Aggregate a r
handles k (Aggregate tally summarize) = Aggregate tally' summarize
  where
    tally' = getConstant . k (Constant . tally)

{-|
>>> fold length ["A","B"]
2
-}
length :: Num n => Aggregate a n
length = Aggregate (\_ -> Sum 1) getSum

{-|
>>> fold sum [1,2,3]
6
-}
sum :: Num n => Aggregate n n
sum = Aggregate Sum getSum

names :: Indexed Int (String, String)
names = group
    [ (0, ("Gabriel", "Gonzalez"))
    , (1, ("Oscar"  , "Boykin"  ))
    , (2, ("Edgar"  , "Codd"    ))
    ]

accounts :: Indexed Int String
accounts = group
    [ (0, "GabrielG439")
    , (1, "posco"      )
    , (3, "avibryant"  )
    ]

{-|
>>> example
group [(0,(("Gabriel","Gonzalez"),Just "GabrielG439")),(1,(("Oscar","Boykin"),Just "posco")),(2,(("Edgar","Codd"),Nothing))]
-}
example :: Indexed Int ((String, String), Maybe String)
example = liftA2 (,) names (optional accounts)
