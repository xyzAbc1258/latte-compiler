{-# LANGUAGE RankNTypes #-}

module Common.Utils where

import qualified Data.Set as Set
import qualified Data.Foldable as Fold
import Control.Lens
import Control.Monad.State
import Data.Maybe
import Control.Applicative


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
        
class Defaultable a where
  getDefault :: a
  
instance Defaultable () where
  getDefault = ()