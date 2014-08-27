{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
module GarbageCollection where

import Control.Lens
import Data.List (mapAccumL, find)

import GraphReduction
import qualified Utils as U
import Utils (Addr, Heap)


data MarkingMachine = MarkingMachine
    { _forwardP    :: Addr
    , _backwardP   :: Addr
    , _machineHeap :: TiHeap
    } deriving (Show)
makeLenses ''MarkingMachine


-- markFromStack, markFromDump, and markFromGlobals are probably the
-- cleverest bits of code here, but easy enough to understand. The goal
-- here is to start from all the possible places that could reference nodes
-- (the stack, dump, and globals) and mark all the nodes which are indeed
-- referenced.
--
-- We use mapAccumL and mapAccumLOf to iteratively update the heap for each
-- "entry point". Folding with the heap as the accumulator.
markFromStack :: TiState -> TiState
markFromStack state = state & stack .~ newStack
                            & heap  .~ newHeap
    where (newHeap, newStack) = mapAccumL markFrom (state^.heap) (state^.stack)


markFromDump :: TiState -> TiState
markFromDump state = state & dump .~ newDump
                           & heap .~ newHeap
    where (newHeap, newDump) = mapAccumLOf
              (traverse.traverse) markFrom (state^.heap) (state^.dump)


markFromGlobals :: TiState -> TiState
markFromGlobals state = state & globals .~ newGlobals
                              & heap    .~ newHeap
    where (newHeap, newGlobals) =
              mapAccumLOf traverse markFrom (state^.heap) (state^.globals)


-- Takes a heap and an address and returns a new heap and address from
-- which all the accessible nodes have been marked.
--
-- Keep running the marking machine over this heap until it's done. TODO
-- - more detail on what running the machine means and what it means to be
-- done
markFrom :: TiHeap -> Addr -> (TiHeap, Addr)
markFrom heap addr = (finalMachine^.machineHeap, finalMachine^.forwardP) where
    startMachine = MarkingMachine addr U.null heap
    machines = iterate runMarkingMachine startMachine
    isFinal machine = (U.isnull $ machine^.backwardP) &&
        (isDone $ machine^.(pointsTo forwardP))
    Just finalMachine = find isFinal machines

    isDone :: Node -> Bool
    isDone (NMarked Done _) = True
    isDone _                = False


-- Get the node pointed to by either forwardP or backwardP
pointsTo :: Getter MarkingMachine Addr -> Getter MarkingMachine Node
pointsTo addrGetter = to $ \machine ->
    U.lookup (machine^.addrGetter) (machine^.machineHeap)


-- (Node -> Node) -> MarkingMachine -> MarkingMachine
nodeAt :: Getter MarkingMachine Addr -> Setter' MarkingMachine Node
nodeAt getter = sets $ \nodeMod machine ->
    -- hope that nodeMod doesn't force its argument
    machine & machineHeap %~ U.update (machine^.getter) (nodeMod undefined)


runMarkingMachine :: MarkingMachine -> MarkingMachine
runMarkingMachine machine = case machine^.(pointsTo forwardP) of
    NAp a1 a2 -> machine & backwardP       .~ f
                         & nodeAt forwardP .~
                             NMarked (Visits 1) (NAp b a2)
                         & forwardP        .~ a1
    NData tag (p:ps) -> machine & backwardP       .~ f
                                & nodeAt forwardP .~
                                    NMarked (Visits 1) (NData tag (b:ps))
                                & forwardP        .~ p

    -- these are all the same
    node@(NData _ []) ->
        machine & (nodeAt forwardP) .~ (NMarked Done node)
    node@(NPrim _ _) ->
        machine & (nodeAt forwardP) .~ (NMarked Done node)
    node@(NSupercomb _ _ _) ->
        machine & (nodeAt forwardP) .~ (NMarked Done node)
    node@(NNum _) ->
        machine & (nodeAt forwardP) .~ (NMarked Done node)

    -- If we come across a node with some visits we're circularly seeing
    -- it. Back slowly away from the node...
    --
    -- If it's marked as done we're returning to it through sharing. We
    -- still don't need to do anything.
    NMarked _ _ -> dispatchReturnVisit $ machine^.(pointsTo backwardP)

    NInd a -> machine & forwardP .~ a
    where f = machine^.forwardP
          b = machine^.backwardP
          dispatchReturnVisit (NMarked (Visits 1) (NAp b' a2)) =
              machine & nodeAt backwardP .~ NMarked (Visits 2) (NAp f b')
                      & forwardP         .~ a2
          dispatchReturnVisit (NMarked (Visits 2) (NAp a1 b')) =
              machine & nodeAt backwardP .~ NMarked Done (NAp a1 f)
                      & forwardP         .~ b
                      & backwardP        .~ b'
          dispatchReturnVisit (NMarked (Visits n) (NData tag components))
              | n < length components
              = let newComponents = components
                        & ix (n-1) .~ (machine^.forwardP)
                        & ix n     .~ (machine^.backwardP)
                    newForward = components^?!ix n
                in machine & nodeAt backwardP .~
                             NMarked (Visits (n+1)) (NData tag newComponents)
                           & forwardP .~ newForward

              | otherwise
              = let newComponents = components & ix (n-1) .~ f
                in machine & nodeAt backwardP .~
                                NMarked Done (NData tag newComponents)
                           & forwardP         .~ b
                           & backwardP        .~ (last components)
          dispatchReturnVisit x = error (show x ++ show machine)


scanHeap :: TiState -> TiState
scanHeap state = state & heap .~ newHeap where
    addrs = U.addresses (state^.heap)
    newHeap = foldl (\heap' addr -> case U.lookup addr heap' of
        NMarked state node -> U.update addr node heap'
        _                  -> U.free addr heap'
        ) (state^.heap) addrs


gc :: TiState -> TiState
gc = scanHeap . markFromStack . markFromDump . markFromGlobals
