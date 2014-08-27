{-# LANGUAGE OverloadedStrings #-}
module Pretty where

import Control.Lens
import qualified Data.IntMap.Lazy as M
import Data.Text hiding (length, intersperse, last, map, head, zip, drop,
                        mapAccumL, foldl', tail, null, concat, foldl, foldl1,
                        dropWhile, find)
import Text.PrettyPrint.Leijen.Text
import Data.Text.Lazy (fromStrict, toStrict)

import GraphReduction
import qualified Utils as U
import Utils (Addr, Heap)

showResults :: [TiState] -> Text
showResults states = toStrict . displayT . renderPretty 0.9 80 $
    vsep [hsep $ map showState states, showStats $ last states]

showState :: TiState -> Doc
showState state = showStack (state^.heap) (state^.stack) <> line

showHeap :: TiHeap -> Doc
showHeap heap = vcat
    [ text " Heap ["
    , nest 2 $ vsep $ map (text . fromStrict . pack . show) $ M.toList (heap^.U.map)
    , text " ]"
    ]

showStack :: TiHeap -> TiStack -> Doc
showStack heap stack = hcat
    [ text "Stk ["
    , line
    , nest 2 $ vsep $ map showStackItem stack
    , line
    , text " ]"
    ]
    where
        showStackItem addr = hcat
            [ showFWAddr addr
            , text ": "
            , showStkNode heap $ U.lookup addr heap
            ]

showStkNode :: TiHeap -> Node -> Doc
showStkNode heap (NAp funAddr argAddr) = hcat
    [ text "NAp "
    , showFWAddr funAddr
    , text " "
    , showFWAddr argAddr
    , text " ("
    , showNode $ heap^.to (U.lookup argAddr)
    , text ")"
    ]
showStkNode heap node = showNode node

showNode :: Node -> Doc
showNode (NAp a1 a2) = hcat
    [ text "NAp "
    , showAddr a1
    , text " "
    , showAddr a2
    ]
showNode (NSupercomb name args body) = text $ fromStrict $ "NSupercomb " `append` name
showNode (NNum n) = text "NNum " <> int n
showNode (NInd p) = text "Indirection " <> int p
showNode (NPrim name _) = "Prim " <> (text $ fromStrict name)
showNode (NData tag components) = "NData " <> int tag

showAddr :: Addr -> Doc
showAddr addr = int addr
showFWAddr addr = indent (4 - (length $ show addr)) $ int addr where

showStats :: TiState -> Doc
showStats state = hcat
    [ line
    , text "Total number of steps = "
    , int $ tiStatGetSteps $ state^.stats
    , line
    ]
