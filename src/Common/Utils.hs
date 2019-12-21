{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Common.Utils where

import qualified Data.Set as Set
import qualified Data.Foldable as Fold
import Control.Lens
import Control.Monad.State
import Data.Maybe
import Control.Applicative

import Data.List as List
import Data.List.Split as Ls



replace from to = intercalate to . Ls.splitOn from

type E a = a -> a

unique::(Foldable t, Ord a) => t a -> Bool
unique c = let l = Fold.toList c
             in let set = Set.fromList l
               in length l == length set

mapStateType::(Monad m) => Lens' a b -> StateT b m r -> StateT a m r
mapStateType lens ms = StateT $ \s -> runStateT ms (s ^. lens) >>= (\(r, f) -> return (r, set lens f s))

orElse::Maybe a -> a -> a
orElse m e = fromJust $ m <|> Just e

liftEndo:: Lens' a b -> E b -> E a
liftEndo l f x = set' l (f $ x ^. l) x

splitOn::(a -> Bool) -> [a] -> [[a]]
splitOn pred coll = _splitOn id coll []
  where _splitOn f [] r = reverse $filter (not . null) $ f [] : r
        _splitOn f (h:t) r = if pred h then _splitOn id t ([h] : f [] : r) else _splitOn (f . (h :)) t r
        
class (Show a) => Defaultable a where
  getDefault :: a
  
instance Defaultable () where
  getDefault = ()
  
  
groupByFirst::(Eq a) => [(a, b)] -> [(a, [b])]
groupByFirst l = 
  let keys = nub $ map fst l in
  let p = map (\k -> (k, map snd $ filter (( == k) . fst) l)) keys in
  p

flatten::(Foldable t, Foldable f) => t (f a) -> [a]
flatten = foldMap Fold.toList