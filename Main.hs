{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad
import qualified Data.Text.IO as T

import Data.Text.Lazy (fromStrict, toStrict)
import Text.PrettyPrint.Leijen.Text

import GraphReduction

main :: IO ()
main = do
--     -- main = S K K 3
--     -- > 3
--     T.putStrLn $ showResults $ eval $ compile [("main", [],
--         EAp
--             (EAp
--                 (EAp
--                     (EVar "S")
--                     (EVar "K"))
--                 (EVar "K"))
--             (ENum 3)
--         )]
--     T.putStrLn $ showResults $ eval $ compile [("main", [], EAp (EVar "I") (ENum 3))]
--
--     -- main = let x = 3; y = I in y x
--     -- > 3
--     T.putStrLn $ showResults $ eval $ compile [("main", [],
--         ELet NonRecursive [("x", ENum 3), ("y", EVar "I")]
--             (EAp (EVar "y") (EVar "x")))]
--
--     {-
--     - pair x y f = f x y
--     - fst p = p K
--     - snd p = p K1
--     - f x y = letrec
--     -   a = pair x b
--     -   b = pair y a
--     -   in fst (snd (snd (snd a)))
--     - main = f 3 4
--     -
--     - > 4
--     -}
--     T.putStrLn $ showResults $ eval $ compile
--         [ ("main", [], EAp (EAp (EVar "f") (ENum 3)) (ENum 4))
--         , ("pair", ["x", "y", "f"], EAp (EAp (EVar "f") (EVar "x")) (EVar "y"))
--         , ("fst", ["p"], EAp (EVar "p") (EVar "K"))
--         , ("snd", ["p"], EAp (EVar "p") (EVar "K1"))
--         , ("f", ["x", "y"], ELet Recursive
--               [ ("a", EAp (EAp (EVar "pair") (EVar "x")) (EVar "b"))
--               , ("b", EAp (EAp (EVar "pair") (EVar "y")) (EVar "a"))
--               ]
--               (EAp (EVar "fst")
--                    (EAp (EVar "snd")
--                         (EAp (EVar "snd")
--                              (EAp (EVar "snd")
--                                   (EVar "a"))))))
--         ]
--
--     -- id x = x
--     -- main = twice twice id 3
--     T.putStrLn $ showResults $ eval $ compile
--         [ ("id", ["x"], EVar "x")
--         , ("main", [], EAp
--                            (EAp
--                                (EAp (EVar "twice")
--                                     (EVar "twice"))
--                                (EVar "id"))
--                            (ENum 3))
--         ]

    let evaled = eval $ compile [("main", [], EAp (EVar "negate") (ENum 3))]

    forM_ evaled $ \e ->
        T.putStrLn $ toStrict $ displayT $ renderPretty 0.9 80 $ showState e

    -- main = negate 3
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EVar "negate") (ENum 3))]

    -- main = twice negate 3
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp
                          (EAp
                              (EVar "twice")
                              (EVar "negate"))
                          (ENum 3))
        ]

    -- main = negate (I 3)
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EVar "negate")
                          (EAp (EVar "I") (ENum 3)))
        ]

    -- main = 1 + 2
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EAp (EVar "+")
                               (ENum 1))
                          (ENum 2))
        ]

    -- main = 1 - 2
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EAp (EVar "-")
                               (ENum 1))
                          (ENum 2))
        ]

    -- main = 1 * 2
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EAp (EVar "*")
                               (ENum 1))
                          (ENum 2))
        ]

    -- main = 1 / 2
    T.putStrLn $ showResults $ eval $ compile
        [("main", [], EAp (EAp (EVar "/")
                               (ENum 1))
                          (ENum 2))
        ]
