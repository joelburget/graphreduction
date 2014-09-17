{-# LANGUAGE OverloadedStrings #-}

module Machine.Internal.Defs where

import Machine.Internal.Data

-- primitives :: H.HashMap Name Primitive
primitives :: [(Name, Primitive)]
primitives =
    [ ("negate", Neg)
    , ("+", Add), ("-", Sub)
    , ("*", Mul), ("/", Div)
    , ("if", If)
    , (">", Greater), (">=", GreaterEq)
    , ("<", Less), ("<=", LessEq)
    , ("==", Eq), ("!=", NotEq)
    , ("casePair", CasePair)
    , ("abort", Abort)
    , ("caseList", CaseList)
    , ("print", Print), ("stop", Stop)
    ]

preludeDefs :: CoreProgram
preludeDefs =
    [ ("I",  ["x"], EVar "x")
    , ("K",  ["x", "y"], EVar "x")
    , ("K1", ["x", "y"], EVar "y")
    , ("S",  ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x"))
                                  (EAp (EVar "g") (EVar "x")))
    , ("compose", ["f", "g", "x"], EAp (EVar "f")
                                       (EAp (EVar "g") (EVar "x")))
    , ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))
    , ("False", [], EConstr 1 0)
    , ("True", [], EConstr 2 0)
    , ("fst", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K"))
    , ("snd", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K1"))
    , ("MkPair", [], EConstr 1 2)
    , ("Nil", [], EConstr 1 0)
    , ("Cons", [], EConstr 2 2)
    -- TODO - hide this in a let
    , ("head'", ["x", "xs"], EVar "x")
    , ("head", ["lst"], EAp (EAp (EAp (EVar "caseList")
                                      (EVar "lst"))
                                 (EVar "abort"))
                            (EVar "head'"))
    -- TODO - hide this in a let
    , ("tail'", ["x", "xs"], EVar "xs")
    , ("tail", ["lst"], EAp (EAp (EAp (EVar "caseList")
                                      (EVar "lst"))
                                 (EVar "abort"))
                            (EVar "tail'"))
    , ("printList", ["xs"], EAp (EAp (EAp (EVar "caseList")
                                          (EVar "xs"))
                                     (EVar "stop"))
                                (EVar "printCons"))
    , ("printCons", ["h", "t"], EAp (EAp (EVar "print")
                                         (EVar "h"))
                                    (EAp (EVar "printList")
                                         (EVar "t")))
    ]
