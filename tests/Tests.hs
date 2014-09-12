{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.IntMap.Lazy as M hiding (size, map)

import Control.Lens
import Control.Monad (forM_)

import Test.Framework (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit

import Test.HUnit ((@?=), assertEqual, Assertion)

import qualified Machine.GarbageCollection as GC
import Machine.GarbageCollection (forwardP, backwardP, machineHeap)
import Machine.GraphReduction
    -- ( Expr(..)
    -- , Primitive(..)
    -- , PreludeAndPrims(..)
    -- , TiState(..)
    -- )
import Machine.Utils(Heap(..))
import Machine.Run
import qualified Machine.Utils as U
import Machine.Utils (size)


main :: IO ()
main = defaultMain tests


tests :: [Test]
tests =
  [ testGroup "gc" gcTests
  ]


gcTests :: [Test]
gcTests =
  [ testCase "trouble_compile" test_trouble_compile
  , testCase "trouble_results" test_trouble_results
  , testCase "machine_steps" test_machine_steps
  ]


troubleDefs :: PreludeAndPrims
troubleDefs = PreludeAndPrims
    [ ("fst", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K"))
    , ("snd", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K1"))
    , ("MkPair", [], EConstr 1 2)
    , ("K",  ["x", "y"], EVar "x")
    , ("K1", ["x", "y"], EVar "y")
    ]
    [ ("casePair", CasePair) ]


trouble :: TiState
trouble = compileWith troubleDefs [("main", [],
    EAp (EVar "fst")
        (EAp (EVar "snd")
             (EAp (EVar "fst")
                  (EAp (EAp (EVar "MkPair")
                            (EAp (EAp (EVar "MkPair")
                                      (ENum 1))
                                 (EAp (EAp (EVar "MkPair")
                                           (ENum 2))
                                      (ENum 3))))
                       (ENum 4))))
    )]


test_trouble_compile :: Assertion
test_trouble_compile = (trouble^.heap^.size) @?= 7


test_trouble_results :: Assertion
test_trouble_results = do
    let lastState = last $ eval trouble
        heap' = lastState^.heap
        stack' = lastState^.stack
    -- sz <- heap'^.size
    -- assertEqual "reduces to one node" sz 1

    let node = U.lookup (head stack') heap'
    assertEqual "correct answer" node (NNum 2)


test_machine_steps :: Assertion
test_machine_steps = do
    let heap' = Heap 3 [4..] $ M.fromList
            [ (1, NData 1 [2, 3])
            , (2, NNum 2)
            , (3, NNum 3)
            ]
        stack' = [1]
        startMachine = GC.MarkingMachine 1 U.null heap'

    let machine1 = GC.runMarkingMachine startMachine
    (machine1^.forwardP) @?= 2
    (machine1^.backwardP) @?= 1
    (machine1^.machineHeap^.U.map^.at 1) @?=
        (Just $ NMarked (Visits 1) (NData 1 [0, 3]))
    (machine1^.machineHeap^.U.map^.at 2) @?= (Just $ NNum 2)

    let machine2 = GC.runMarkingMachine machine1
    (machine2^.forwardP) @?= 2
    (machine2^.backwardP) @?= 1
    (machine2^.machineHeap^.U.map^.at 1) @?=
        (Just $ NMarked (Visits 1) (NData 1 [0, 3]))
    (machine2^.machineHeap^.U.map^.at 2) @?= (Just $ (NMarked Done (NNum 2)))

    let machine3 = GC.runMarkingMachine machine2
    (machine3^.forwardP) @?= 3
    (machine3^.backwardP) @?= 1
    (machine3^.machineHeap^.U.map^.at 1) @?=
        (Just $ NMarked (Visits 2) (NData 1 [2, 0]))
    (machine3^.machineHeap^.U.map^.at 3) @?= (Just $ NNum 3)

    let machine4 = GC.runMarkingMachine machine3
    (machine4^.forwardP) @?= 3
    (machine4^.backwardP) @?= 1
    (machine4^.machineHeap^.U.map^.at 1) @?=
        (Just $ NMarked (Visits 2) (NData 1 [2, 0]))
    (machine4^.machineHeap^.U.map^.at 3) @?= (Just $ (NMarked Done (NNum 3)))

    let machine5 = GC.runMarkingMachine machine4
    (machine5^.forwardP) @?= 1
    (machine5^.backwardP) @?= 0
    (machine5^.machineHeap^.U.map^.at 1) @?=
        (Just $ NMarked Done (NData 1 [2, 3]))
