
module Language.Prolog2.NamedGraph
       ( NamedGraph(..)
       , empty
       , merge
       ) where

#ifdef YESOD
import Prelude
#endif

import Data.Graph.Inductive.Graph hiding (empty)
import qualified Data.Graph.Inductive.Graph  as Graph
import Data.Graph.Inductive.PatriciaTree(Gr)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.List
import Data.Maybe

data NamedGraph a = NamedGraph { ngGraph :: Gr a ()
                               , ngMap   :: Map a Node
                               }

empty :: Ord a => NamedGraph a
empty = NamedGraph Graph.empty Map.empty

merge :: (Ord a) => NamedGraph a -> NamedGraph a -> NamedGraph a
merge (NamedGraph gr1 map1) (NamedGraph gr2 map2) =
  let map3 = mergeMap map1 map2
      gr1' = translateGraph map3 gr1
      gr2' = translateGraph map3 gr2
      gr3  = unionGraph gr1' gr2'
  in NamedGraph gr3 map3

mergeMap :: Ord a => Map a Node -> Map a Node -> Map a Node
mergeMap m1 m2  = let m3 = Map.union m1 m2
                  in Map.fromList $ zip (Map.keys m3) [0..]


translateGraph :: Ord a => Map a Node -> Gr a () -> Gr a ()
translateGraph m gr = ufold append Graph.empty  gr
  where
    nodeMap :: Node -> Maybe Node
    nodeMap n = case lab gr n of
      Just a ->  Map.lookup a m
      Nothing -> Nothing

    adjMap :: ((), Node ) -> Maybe ((), Node)
    adjMap ((),n ) = (\x -> ((), x)) <$> nodeMap n

    append :: Context a () -> Gr a () -> Gr a ()
    append (ins ,node ,a ,outs) gr' =
      case nodeMap node of
      Just nodeNew -> (mapMaybe adjMap ins, nodeNew, a , mapMaybe adjMap outs) & gr'
      Nothing    -> gr'

unionGraph :: (Eq a, Ord a) => Gr a () -> Gr a () -> Gr a ()
unionGraph gr1 gr2 = ufold mergeContext gr2 gr1
  where
    mergeContext :: Eq a => Context a () -> Gr a () -> Gr a ()
    mergeContext (ins, node, a, outs) gr = case match node gr of
      (Just (ins', n, a', outs') , gr') -> if node == n && a == a'
                                           then (unionAdj ins ins', node , a, unionAdj outs outs') & gr'
                                           else error "unionGraph: argument error"
      (Nothing , gr') -> (ins, node, a, outs) & gr'

    unionAdj :: Adj () -> Adj () -> Adj ()
    unionAdj as bs =  nub (as ++ bs)
