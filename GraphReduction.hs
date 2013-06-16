{-# LANGUAGE OverloadedStrings #-}
-- Implementing Functional Languages: a tutorial
-- Template Instantiation language
module GraphReduction where

import qualified Data.IntMap.Lazy as M
import qualified Data.HashMap.Lazy as H
import Data.List (intersperse, mapAccumL, foldl')
import Data.Text hiding (length, intersperse, last, map, head, zip, drop,
                        mapAccumL, foldl')
import Data.Text.Lazy (fromStrict, toStrict)
import Text.PrettyPrint.Leijen.Text
import Prelude hiding (intersperse)

import Utils

data Expr a
    = EVar Name             -- ^ variable
    | ENum Int              -- ^ number
    | EConstr Int Int       -- ^ Constructor tag arity
    | EAp (Expr a) (Expr a) -- ^ application
    | ELet                  -- ^ Let(rec) expression
        IsRec               -- body with True = recursive
        [(a, Expr a)]       -- definitions
        (Expr a)            -- body
    | ECase                 -- ^ Case expression
        (Expr a)            -- expression to scrutinize
        [Alter a]           -- alternatives
    | ELam [a] (Expr a)     -- ^ Lambda abstraction

type CoreExpr = Expr Name
type Name = Text

-- | Is this let recursive?
data IsRec = Recursive | NonRecursive

-- | Picks out the list of variables bound by definitions
bindersOf :: [(a, b)] -> [a]
bindersOf defns = [name | (name, rhs) <- defns]

rhssOf :: [(a, b)] -> [b]
rhssOf defns = [rhs | (name, rhs) <- defns]

-- | Alternative - containing a tag, list of bound variables, and
-- expression to the right of the arrow
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar v) = True
isAtomicExpr (ENum n) = True
isAtomicExpr _ = False

type Program a = [ScDefn a]
type CoreProgram = Program Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

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
    ]

-- begin ch 2

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

-- The spine stack is a stack of heap addresses
type TiStack = [Addr]

data TiDump = DummyTiDump
initialTidump = DummyTiDump

type TiHeap = Heap Node

data Node
    = NAp Addr Addr                   -- Application
    | NSupercomb Name [Name] CoreExpr -- Supercombinator
    | NNum Int                        -- Number
    | NInd Addr                       -- Indirection

type TiGlobals = H.HashMap Name Addr

tiStatInitial :: TiStats
tiStatIncSteps :: TiStats -> TiStats
tiStatGetSteps :: TiStats -> Int

type TiStats = Int
tiStatInitial = 0
tiStatIncSteps = (+1)
tiStatGetSteps = id

-- TODO use lens
applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats stats_fun (stack, dump, heap, sc_defs, stats) =
    (stack, dump, heap, sc_defs, stats_fun stats)

-- | create the initial state of the machine from the program
compile :: CoreProgram -> TiState
compile program =
    (initial_stack, initialTidump, initial_heap, globals, tiStatInitial)
    where
        sc_defs = program ++ preludeDefs ++ extraPreludeDefs
        (initial_heap, globals) = buildInitialHeap sc_defs

        initial_stack = [address_of_main]
        address_of_main = H.lookupDefault (error "main is not defined") "main" globals

extraPreludeDefs = []

-- TODO lens
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap sc_defs = (heap, H.fromList globalsLst)
    where (heap, globalsLst) = mapAccumL allocateSc hInitial sc_defs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = hAlloc heap (NSupercomb name args body)

eval :: TiState -> [TiState]
eval state = state:rest_states where
    rest_states | tiFinal state = []
                | otherwise = eval next_state
    next_state = doAdmin $ step state

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

tiFinal :: TiState -> Bool
tiFinal ([sole_addr], _, heap, _, _)
    = isDataNode $ hLookup heap sole_addr
tiFinal ([], _, _, _, _) = error "Empty stack!"
tiFinal state = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode node = False

step :: TiState -> TiState
step state = dispatch $ hLookup heap $ head stack where
    (stack, dump, heap, globals, stats) = state
    dispatch (NNum n) = numStep state n
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    --         a :s    d    h[a:NInd a1]    f
    --     ==> a1:s    d    h               f
    dispatch (NInd a1) = (a1 : (drop 1 stack), dump, hFree heap (head stack),
        globals, stats) -- TODO update stats?

numStep :: TiState -> Int -> TiState
numStep _ _ = error "Number applied as a function!"

-- TODO use lens
apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 _ =
    (a1:stack, dump, heap, globals, stats)

-- | Step a supercombinator. Described by the transition rule:
--
--         a0:a1:...:an:s    d    h[a0:NSupercomb[x1, ..., xn] body]    f
--     ==>           ar:s    d    h'[an:NInd ar]                        f
--     where (h', ar) = instantiate body h f [x1 -> a1, ..., xn -> an]
--
-- In other words, overwrite node an (the root of the redex) with an
-- indirection to ar (the root of the result). If the supercombinator is
-- a CAF then n=0 and the node to be modified is the supercombinator node
-- itself.
scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) sc_name arg_names body =
    (new_stack, dump, new_heap, globals, stats)
    where
    new_stack = drop (length arg_names) stack
    arg_bindings = zip arg_names $ getargs heap stack
    env = H.union (H.fromList arg_bindings) globals
    body_addr = head new_stack
    new_heap = instantiateAndUpdate body body_addr heap env

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:stack) = map get_arg stack where
    get_arg addr = arg where (NAp fun arg) = hLookup heap addr

{-
 - Instantiate the given supercombinator body, writing over the given
 - address, if possible
 -}
instantiateAndUpdate :: CoreExpr            -- ^ body of supercombinator
                     -> Addr                -- ^ address of node to update
                     -> TiHeap              -- ^ heap before instantiation
                     -- | associate parameters to addresses
                     -> H.HashMap Name Addr
                     -> TiHeap              -- ^ heap after instantiation
instantiateAndUpdate (ENum n) upd_addr heap _ = hUpdate heap upd_addr $ NNum n
-- replace the old application with the result of instantiation
instantiateAndUpdate (EAp e1 e2) upd_addr heap env =
    hUpdate heap2 upd_addr (NAp a1 a2)
    where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env
instantiateAndUpdate ev@(EVar v) upd_addr heap env =
    hUpdate heap' upd_addr $ NInd addr
    where
    (heap', addr) = instantiate ev heap env
instantiateAndUpdate (EConstr tag arity) upd_addr heap env = error "Not yet!"
instantiateAndUpdate (ELet isrec defs body) upd_addr heap env =
    instantiateAndUpdateLet isrec defs body upd_addr heap env
instantiateAndUpdate (ECase e alts) upd_addr heap env = error "Not yet!"

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateAndUpdateLet isrec defs body upd_addr heap env = result where
    (resultHeap, resultEnv) = foldl' (\(heap', env') (a, expr) ->
        let thisEnv = case isrec of
                Recursive -> resultEnv
                NonRecursive -> env'
            (heap'', addr) = (instantiate expr heap' thisEnv)
            env'' = H.insert a addr env'
        in (heap'', env'')) (heap, env) defs
    result = instantiateAndUpdate body upd_addr resultHeap resultEnv

instantiate :: CoreExpr -- ^ body of supercombinator
            -> TiHeap   -- ^ heap before instantiation
            -> H.HashMap Name Addr -- ^ association of names to addresses
            -- | heap after instantiation and address of root of instance
            -> (TiHeap, Addr)
instantiate (ENum n) heap _ = hAlloc heap $ NNum n
instantiate (EAp e1 e2) heap env = hAlloc heap2 $ NAp a1 a2 where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env =
    (heap, H.lookupDefault (error $ "Undefined name " ++ show v) v env)
instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env
instantiate (ELet isrec defs body) heap env =
    instantiateLet isrec defs body heap env
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"

instantiateConstr _ _ _ _ = error "Can't instantiate constructors yet"

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateLet isrec defs body heap env = result where
    (resultHeap, resultEnv) = foldl' (\(heap', env') (a, expr) ->
        let thisEnv = case isrec of
                Recursive -> resultEnv
                NonRecursive -> env'
            (heap'', addr) = (instantiate expr heap' thisEnv)
            env'' = H.insert a addr env'
        in (heap'', env'')) (heap, env) defs
    result = instantiate body resultHeap resultEnv

showResults :: [TiState] -> Text
showResults states = toStrict . displayT . renderPretty 0.9 80 $
    vsep [hsep $ map showState states, showStats $ last states]

showState :: TiState -> Doc
showState (stack, _, heap, _, _) = showStack heap stack <> line

showStack :: TiHeap -> TiStack -> Doc
showStack heap stack = hcat
    [ text "Stk ["
    , line
    , nest 2 $ vsep $ map show_stack_item stack
    , line
    , text " ]"
    ]
    where
        show_stack_item addr = hcat
            [ showFWAddr addr
            , text ": "
            , showStkNode heap $ hLookup heap addr
            ]

showStkNode :: TiHeap -> Node -> Doc
showStkNode heap (NAp fun_addr arg_addr) = hcat
    [ text "NAp "
    , showFWAddr fun_addr
    , text " "
    , showFWAddr arg_addr
    , text " ("
    , showNode $ hLookup heap arg_addr
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

showAddr :: Addr -> Doc
showAddr addr = int addr
showFWAddr addr = indent (4 - (length $ show addr)) $ int addr where

showStats :: TiState -> Doc
showStats (_, _, _, _, stats) = hcat
    [ line
    , text "Total number of steps = "
    , int $ tiStatGetSteps stats
    , line
    ]
