{-# LANGUAGE OverloadedStrings #-}
module Machine.Run where

import Control.Lens
import Data.Maybe (fromMaybe)

import Machine.GraphReduction
import Machine.GarbageCollection
import Machine.Step
import qualified Machine.Utils as U

compileWith :: PreludeAndPrims -> CoreProgram -> TiState
compileWith defs program =
    TiState [] initialStack initialTidump initialHeap globals tiStatInitial
    where
        scDefs = prelude defs ++ program
        (initialHeap, globals) = buildInitialHeap scDefs (prims defs)

        addressOfMain = fromMaybe (error "main is not defined") $
            globals ^? ix "main"
        initialStack = [addressOfMain]

-- | create the initial state of the machine from the program
compile :: CoreProgram -> TiState
compile = compileWith (PreludeAndPrims preludeDefs primitives)

-- TODO only gc when heap is bigger than some size
doAdmin :: TiState -> TiState
doAdmin = gc . (& (stats +~ 1))

tiFinal :: TiState -> Bool
tiFinal state = case state^.stack of
    [] -> True
    [soleAddr] -> dataNode && emptyDump
        where dataNode = isDataNode $ U.lookup soleAddr (state^.heap)
              emptyDump = null $ state^.dump
    _ -> False

eval :: TiState -> [TiState]
eval state = state:restStates where
    restStates | tiFinal state = []
               | otherwise = eval nextState
    nextState = doAdmin $ step state
