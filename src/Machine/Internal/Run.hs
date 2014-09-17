{-# LANGUAGE OverloadedStrings #-}
module Machine.Internal.Run where

import Control.Lens
import Data.Maybe (fromMaybe)

import Machine.Internal.Data
import Machine.Internal.Defs
import Machine.Internal.GC.MarkScan
import qualified Machine.Internal.Heap as U
import Machine.Internal.Step

compileWith :: PreludeAndPrims -> CoreProgram -> State
compileWith defs program =
    State [] initialStack initialdump initialHeap globals tiStatInitial
    where
        scDefs = prelude defs ++ program
        (initialHeap, globals) = buildInitialHeap scDefs (prims defs)

        addressOfMain = fromMaybe (error "main is not defined") $
            globals ^? ix "main"
        initialStack = [addressOfMain]

-- | create the initial state of the machine from the program
compile :: CoreProgram -> State
compile = compileWith (PreludeAndPrims preludeDefs primitives)

-- TODO only gc when heap is bigger than some size
doAdmin :: State -> State
doAdmin = gc . (& (stats +~ 1))

tiFinal :: State -> Bool
tiFinal state = case state^.stack of
    [] -> True
    [soleAddr] -> dataNode && emptyDump
        where dataNode = isDataNode $ U.lookup soleAddr (state^.heap)
              emptyDump = null $ state^.dump
    _ -> False

eval :: State -> [State]
eval state = state:restStates where
    restStates | tiFinal state = []
               | otherwise = eval nextState
    nextState = doAdmin $ step state
