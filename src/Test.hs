module Test
       where
import Prelude
import Language.Prolog2.NamedGraph
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Map(Map)
import qualified Data.Map as Map

gr1 :: Gr String ()
gr1 = buildGr [ ([((),0)], 1, "b" , [] )
              , ([((),0)], 2, "c" , [] )
              , ([] , 0 , "a" , [] )
              ]

map1 :: Map String Node
map1 = Map.fromList [("a",0),("b",1),("c",2) ]


gr2 :: Gr String ()
gr2 = buildGr [ ([((),0)], 1, "d" , [] )
              , ([((),0)], 2, "e" , [] )
              , ([] , 0 , "c" , [] )
              ]

map2 :: Map String Node
map2 = Map.fromList [("c",0),("d",1),("e",2) ]

gr3 :: Gr String ()
gr3 = buildGr [ ([((),1)], 3, "f" , [] )
              , ([((),1)], 2, "d" , [] )
              , ([] , 1 , "c" , [] )
              ]

map3 :: Map String Node
map3 = Map.fromList [("c",1),("d",2),("f",3) ]


ng1 = merge (NamedGraph gr1 map1) (NamedGraph gr2 map2)

ng2 = merge (NamedGraph gr2 map2) (NamedGraph gr3 map3)
