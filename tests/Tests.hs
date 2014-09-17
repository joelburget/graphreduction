{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.IntMap.Lazy as M hiding (size, map)

import Control.Lens

import Test.Framework (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit

import Test.HUnit ((@?=), assertEqual, Assertion)

import qualified Machine as GC
import qualified Machine as U
import Machine (
    CoreProgram,
    Expr(..),
    Heap(..),
    MarkState(..),
    Node(..),
    PreludeAndPrims(..),
    Primitive(..),
    TiState,

    backwardP,
    compile,
    compileWith,
    eval,
    forwardP,
    heap,
    machineHeap,
    output,
    size,
    stack
    )

main :: IO ()
main = defaultMain tests


tests :: [Test]
tests =
  [ testGroup "gc" gcTests
  , testGroup "exec" execTests
  ]


gcTests :: [Test]
gcTests =
  [ testCase "trouble_compile" test_trouble_compile
  , testCase "trouble_results" test_trouble_results
  , testCase "machine_steps" test_machine_steps
  ]


execTests :: [Test]
execTests =
    [ testCase "exec 1" exec_example_1
    , testCase "exec 2" exec_example_2
    , testCase "exec 3" exec_example_3
    , testCase "exec 4" exec_example_4
    , testCase "exec 5" exec_example_5
    , testCase "exec 6" exec_example_6
    , testCase "exec 7" exec_example_7
    , testCase "exec 8" exec_example_8
    , testCase "exec 9" exec_example_9
    , testCase "exec 10" exec_example_10
    , testCase "exec 11" exec_example_11
    , testCase "exec 12" exec_example_12
    , testCase "exec 13" exec_example_13
    , testCase "exec 14" exec_example_14
    , testCase "exec 15" exec_example_15
    , testCase "exec 16" exec_example_16
    , testCase "exec 17" exec_example_17
    , testCase "exec 18" exec_example_18
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

    let node = U.lookup (head stack') heap'
    assertEqual "correct answer" node (NNum 2)


test_machine_steps :: Assertion
test_machine_steps = do
    let heap' = Heap 3 [4..] $ M.fromList
            [ (1, NData 1 [2, 3])
            , (2, NNum 2)
            , (3, NNum 3)
            ]
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


extractResult :: [TiState] -> Node
extractResult states =
    let finalState = last states
        finalStack = finalState^.stack
        finalHeap = finalState^.heap
        finalNode = U.lookup (head finalStack) finalHeap
    in finalNode

getFinalNode :: CoreProgram -> Node
getFinalNode = extractResult . eval . compile

exec_example_1 :: Assertion
exec_example_1 = do
    -- main = S K K 3
    -- > 3
    let x = getFinalNode [("main", [],
            EAp
                (EAp
                    (EAp
                        (EVar "S")
                        (EVar "K"))
                    (EVar "K"))
                (ENum 3)
            )]

    x @?= NNum 3

exec_example_2 :: Assertion
exec_example_2 = do
    let x = getFinalNode [("main", [], EAp (EVar "I") (ENum 3))]
    x @?= NNum 3

exec_example_3 :: Assertion
exec_example_3 = do
    -- main = let x = 3; y = I in y x
    -- > 3
    let x = getFinalNode [("main", [],
            ELet [("x", ENum 3), ("y", EVar "I")]
                (EAp (EVar "y") (EVar "x")))]
    x @?= NNum 3

exec_example_4 :: Assertion
exec_example_4 = do
    {-
    - pair x y f = f x y
    - fst p = p K
    - snd p = p K1
    - f x y = letrec
    -   a = pair x b
    -   b = pair y a
    -   in fst (snd (snd (snd a)))
    - main = f 3 4
    -
    - > 4
    -}
    let x = getFinalNode
            [ ("main", [], EAp (EAp (EVar "f") (ENum 3)) (ENum 4))
            , ("pair", ["x", "y", "f"], EAp (EAp (EVar "f") (EVar "x")) (EVar "y"))
            , ("fst", ["p"], EAp (EVar "p") (EVar "K"))
            , ("snd", ["p"], EAp (EVar "p") (EVar "K1"))
            , ("f", ["x", "y"], ELet
                  [ ("a", EAp (EAp (EVar "pair") (EVar "x")) (EVar "b"))
                  , ("b", EAp (EAp (EVar "pair") (EVar "y")) (EVar "a"))
                  ]
                  (EAp (EVar "fst")
                       (EAp (EVar "snd")
                            (EAp (EVar "snd")
                                 (EAp (EVar "snd")
                                      (EVar "a"))))))
            ]
    x @?= NNum 4

exec_example_5 :: Assertion
exec_example_5 = do
    -- id x = x
    -- main = twice twice id 3
    --
    -- > 3
    let x = getFinalNode
            [ ("id", ["x"], EVar "x")
            , ("main", [], EAp
                               (EAp
                                   (EAp (EVar "twice")
                                        (EVar "twice"))
                                   (EVar "id"))
                               (ENum 3))
            ]
    x @?= NNum 3

exec_example_6 :: Assertion
exec_example_6 = do
    -- main = negate 3
    --
    -- > -3
    let x = getFinalNode [("main", [], EAp (EVar "negate") (ENum 3))]
    x @?= NNum (-3)

exec_example_7 :: Assertion
exec_example_7 = do
    -- main = twice negate 3
    --
    -- > 3
    let x = getFinalNode
            [("main", [], EAp
                              (EAp
                                  (EVar "twice")
                                  (EVar "negate"))
                              (ENum 3))
            ]
    x @?= NNum 3

exec_example_8 :: Assertion
exec_example_8 = do
    -- main = negate (I 3)
    --
    -- > -3
    let x = getFinalNode
            [("main", [], EAp (EVar "negate")
                              (EAp (EVar "I") (ENum 3)))
            ]
    x @?= NNum (-3)

exec_example_9 :: Assertion
exec_example_9 = do
    -- main = 1 + 2
    --
    -- > 3
    let x = getFinalNode
            [("main", [], EAp (EAp (EVar "+")
                                   (ENum 1))
                              (ENum 2))
            ]
    x @?= NNum 3

exec_example_10 :: Assertion
exec_example_10 = do
    -- main = 1 - 2
    --
    -- > -1
    let x = getFinalNode
            [("main", [], EAp (EAp (EVar "-")
                                   (ENum 1))
                              (ENum 2))
            ]
    x @?= NNum (-1)

exec_example_11 :: Assertion
exec_example_11 = do
    -- main = 1 * 2
    --
    -- > 2
    let x = getFinalNode
            [("main", [], EAp (EAp (EVar "*")
                                   (ENum 1))
                              (ENum 2))
            ]
    x @?= NNum 2

exec_example_12 :: Assertion
exec_example_12 = do
    -- main = 1 / 2
    --
    -- > 0
    let x = getFinalNode
            [("main", [], EAp (EAp (EVar "/")
                                   (ENum 1))
                              (ENum 2))
            ]
    x @?= NNum 0

exec_example_13 :: Assertion
exec_example_13 = do
    -- main = if False 1 2
    --
    -- > 2
    let x = getFinalNode
            [("main", [], EAp (EAp (EAp (EVar "if")
                                        (EVar "False"))
                                   (ENum 1))
                              (ENum 2))
            ]
    x @?= NNum 2

exec_example_14 :: Assertion
exec_example_14 = do
    -- fac n = if (n == 0) 1 (n * fac (n-1))
    -- main = fac 3
    --
    -- > 6
    let x = getFinalNode
            [("fac", ["n"], EAp (EAp (EAp (EVar "if")
                                          (EAp (EAp (EVar "==")
                                                    (EVar "n"))
                                               (ENum 0)))
                                     (ENum 1))
                                (EAp (EAp (EVar "*")
                                          (EVar "n"))
                                     (EAp (EVar "fac")
                                          (EAp (EAp (EVar "-")
                                                    (EVar "n"))
                                               (ENum 1)))))
            ,("main", [], EAp (EVar "fac") (ENum 3))
            ]
    x @?= NNum 6

exec_example_15 :: Assertion
exec_example_15 = do
    -- main = fst (snd (fst (MkPair (MkPair 1
    --                              (MkPair 2
    --                                      3))
    --                              4)))
    --
    -- > 2
    let x = getFinalNode [("main", [], EAp (EVar "fst")
                          (EAp (EVar "snd")
                               (EAp (EVar "fst")
                                    (EAp (EAp (EVar "MkPair")
                                              (EAp (EAp (EVar "MkPair")
                                                        (ENum 1))
                                                   (EAp (EAp (EVar "MkPair")
                                                             (ENum 2))
                                                        (ENum 3))))
                                         (ENum 4))))) ]
    x @?= NNum 2

exec_example_16 :: Assertion
exec_example_16 = do
    -- main = 1 + fst (MkPair 1 0)
    let x = getFinalNode
            [("main", [], EAp (EAp (EVar "+")
                                   (ENum 1))
                              (EAp (EVar "fst")
                                   (EAp (EAp (EVar "MkPair")
                                             (ENum 1))
                                        (ENum 0))))
            ]
    x @?= NNum 2

exec_example_17 :: Assertion
exec_example_17 = do
    -- length xs = caseList xs 0 length'
    -- length' x xs = 1 + length xs
    -- main = length (Cons 1 Nil)
    let x = getFinalNode
            [("length", ["xs"], EAp (EAp (EAp (EVar "caseList")
                                              (EVar "xs"))
                                         (ENum 0))
                                    (EVar "length'"))
            ,("length'", ["x", "xs"], EAp (EAp (EVar "+")
                                               (ENum 1))
                                          (EAp (EVar "length")
                                               (EVar "xs")))
            ,("main", [], EAp (EVar "length")
                              (EAp (EAp (EVar "Cons")
                                        (ENum 1))
                                   (EVar "Nil")))
            ]
    x @?= NNum 1

exec_example_18 :: Assertion
exec_example_18 = do
    let finalState = last $ eval $ compile $
            [("main", [], EAp (EVar "printList")
                              (EAp (EAp (EVar "Cons")
                                        (ENum 1))
                                   (EVar "Nil")))
            ]

    finalState^.stack @?= []
    finalState^.output @?= [1]
