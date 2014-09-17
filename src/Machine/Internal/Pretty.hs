{-# LANGUAGE OverloadedStrings #-}
module Machine.Internal.Pretty where

import Control.Lens
import qualified Data.IntMap.Lazy as M
import Data.Text hiding (length, intersperse, last, map, head, zip, drop,
                        mapAccumL, foldl', tail, null, concat, foldl, foldl1,
                        dropWhile, find)
import Text.PrettyPrint.Leijen.Text
import Data.Text.Lazy (fromStrict, toStrict)

import Machine.Internal.Data
import qualified Machine.Internal.Heap as U
import Machine.Internal.Heap (Addr)

textify :: Doc -> Text
textify = toStrict . displayT . renderPretty 0.9 80

showResults :: [State] -> Text
showResults states = textify $
    vsep [hsep $ map showState states, showStats $ last states]

showState :: State -> Doc
showState state = showStack (state^.heap) (state^.stack) <> line

tShow :: Show a => a -> Doc
tShow = text . fromStrict . pack . show

showHeap :: Heap -> Doc
showHeap heap = vcat
    [ text " Heap ["
    , nest 2 $ vsep $ map tShow $ M.toList (heap^.U.map)
    , text " ]"
    ]

showStack :: Heap -> Stack -> Doc
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

showStkNode :: Heap -> Node -> Doc
showStkNode heap (NAp funAddr argAddr) = hcat
    [ text "NAp "
    , showFWAddr funAddr
    , text " "
    , showFWAddr argAddr
    , text " ("
    , showNode $ heap^.to (U.lookup argAddr)
    , text ")"
    ]
showStkNode _ node = showNode node

showNode :: Node -> Doc
showNode (NAp a1 a2) = hcat
    [ text "NAp "
    , showAddr a1
    , text " "
    , showAddr a2
    ]
showNode (NSupercomb name _ _) = text $ fromStrict $ "NSupercomb " `append` name
showNode (NNum n) = text "NNum " <> int n
showNode (NInd p) = text "Indirection " <> int p
showNode (NPrim name prim) = "Prim " <> text (fromStrict name) <> " (" <> tShow prim <> ")"
showNode (NData tag _) = "NData " <> int tag

showAddr :: Addr -> Doc
showAddr = int

showFWAddr :: Addr -> Doc
showFWAddr addr = indent (4 - length (show addr)) $ int addr

showStats :: State -> Doc
showStats state = hcat
    [ line
    , text "Total number of steps = "
    , int $ state^.stats
    , line
    ]
