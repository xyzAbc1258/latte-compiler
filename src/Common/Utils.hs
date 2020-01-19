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
import Data.IORef
import System.IO.Unsafe
import Debug.Trace (trace)


isDebugRef::IORef Bool
isDebugRef = unsafePerformIO $ newIORef True
{-# NOINLINE isDebugRef #-}

isDebug::Bool
isDebug = unsafePerformIO $ readIORef isDebugRef
{-# NOINLINE isDebug #-}

setDebug::Bool -> IO ()
setDebug = writeIORef isDebugRef

replace from to = intercalate to . Ls.splitOn from

type E a = a -> a

unique::(Foldable t, Ord a) => t a -> Bool
unique c = let l = Fold.toList c
             in let set = Set.fromList l
               in length l == length set

mapStateType::(Monad m) => Lens' a b -> StateT b m r -> StateT a m r
mapStateType lens ms = StateT $ \s -> runStateT ms (s ^. lens) >>= (\(r, f) -> return (r, set lens f s))

orElse::Maybe a -> a -> a
orElse m e = fromMaybe e m

orElseM::(Monad m) => m (Maybe a) -> m a -> m a
orElseM = liftA2 orElse

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

flatMap::(Foldable f) => (a -> f b) -> [a] -> [b]
flatMap f = flatten . map f

untilStabilizeM::(Eq a ,Monad m) => (a -> m a) -> a -> m a -- poor man's fix :)
untilStabilizeM f a = do
  r <- f a
  if r /= a then untilStabilizeM f r
  else return r

untilStabilize::(Eq a) => E a -> E a
untilStabilize f = runIdentity . untilStabilizeM (Identity . f)

maybeM::(Monad m) => b -> (a -> m b) -> Maybe a -> m b
maybeM def = maybe (return def)

maybeLast::[a] -> Maybe a
maybeLast [] = Nothing
maybeLast a = Just $ last a

--[[1,2],[3,4]] -> [[1,3],[2,4]]
invertList::[[a]] -> [[a]]
invertList l | any null l = []
invertList l = (head <$> l) : invertList (tail <$> l)


traceShow::(Show a) => String -> a -> a
traceShow p o = trace (p ++ show o) o

convertString::String -> String
convertString ('\\':'\\': s) = "\\5C" ++ convertString s
convertString ('\\':'n':s) = "\\0A" ++ convertString s
convertString ('\\':'t':s) = "\\09" ++ convertString s
convertString ('\\':'"':s) = "\\22" ++ convertString s
convertString (c:s) = c : convertString s
convertString [] = []

sLength::String -> Int
sLength ('\\':'5':'C':s) = 1 + sLength s
sLength ('\\':'0':'A':s) = 1 + sLength s
sLength ('\\':'0':'9':s) = 1 + sLength s
sLength ('\\':'2':'2':s) = 1 + sLength s
sLength (_:s) = 1 + sLength s
sLength [] = 0
