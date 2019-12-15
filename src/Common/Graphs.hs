{-# LANGUAGE TupleSections #-}
module Common.Graphs where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative((<|>))
import Common.Utils(orElse,E)


newtype Graph v = Graph{_neighbours :: Map.Map v (Set.Set v)}

fromPairs::(Ord v) => [(v,v)]-> Graph v
fromPairs p = foldl (flip (uncurry add)) empty $ map (\(v,n) -> (v, Set.singleton n)) p

fromList::(Ord v) => [(v, [v])] -> Graph v
fromList = Graph . Map.fromList . fmap (\(k,n) -> (k, Set.fromList n))

modify::E (Map.Map v (Set.Set v)) -> E (Graph v)
modify f = Graph . f . _neighbours

empty::(Ord v) => Graph v
empty = Graph Map.empty

isEmpty::(Ord v) => Graph v -> Bool
isEmpty = null . _neighbours

add::(Ord v) => v -> Set.Set v -> E (Graph v)
add k neigh = modify $ Map.alter (\s -> fmap (Set.union neigh) s <|> Just neigh) k

removeV::(Ord v) => v -> Graph v -> Graph v
removeV k = modify $ Map.delete k

removeN::(Ord v) => (v, v) -> Graph v -> Graph v
removeN (k,v) = modify $ Map.alter (fmap (Set.delete v)) k

neighbours::(Ord v) => v -> Graph v -> Set.Set v
neighbours k g = _neighbours g Map.!? k  `orElse` Set.empty

vertices::(Ord v) => Graph v -> Set.Set v
vertices = Map.keysSet . _neighbours

sortTopologically::(Ord v) => Graph v -> Maybe [v]
sortTopologically g = if hasCycle g then Nothing
                        else Just $ sortTopH g []
                        where sortTopH ng c = if isEmpty ng then c else
                                let withInEdge = foldl Set.union Set.empty $ map (`neighbours` ng) $ Set.toList $ vertices ng
                                  in let withNoInEdge = vertices ng Set.\\ withInEdge in
                                    sortTopH (foldl (flip removeV) ng withNoInEdge) (Set.toList withNoInEdge ++ c)

hasCycle::(Ord v) => Graph v -> Bool
hasCycle g = not (Map.null $ _neighbours g) &&
               (let withInEdge = foldl Set.union Set.empty $ map (`neighbours` g) $ Set.toList $ vertices g
                  in let withNoInEdge = vertices g Set.\\ withInEdge in
                    (null withNoInEdge || hasCycle (foldl (flip removeV) g withNoInEdge)))


depth::(Ord v) => v -> Graph v -> Map.Map v Int
depth start g = depthF [(start,0)] Map.empty
  where depthF [] r = r
        depthF ((h,hl):t) r =
          if Map.member h r then depthF t r
          else let n = Set.toList $ neighbours h g in
                let nt = t ++ ((,hl+1) <$> n) in
                let nr = Map.insert h hl r in
                depthF nt nr