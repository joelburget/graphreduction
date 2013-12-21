{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
-- Implementing Functional Languages: a tutorial
-- Template Instantiation language
module GraphReduction where

import Control.Lens
import qualified Data.IntMap.Lazy as M
import qualified Data.HashMap.Lazy as H
import Data.List (intersperse, mapAccumL, foldl')
import Data.Maybe (fromMaybe)
import Data.Text hiding (length, intersperse, last, map, head, zip, drop,
                        mapAccumL, foldl', tail, null)
import Data.Text.Lazy (fromStrict, toStrict)
import Text.PrettyPrint.Leijen.Text
import Prelude hiding (intersperse)

import qualified Utils as U
import Utils (Addr, Heap)

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
    deriving (Show)

type CoreExpr = Expr Name
type Name = Text

-- | Is this let recursive?
data IsRec = Recursive | NonRecursive deriving (Show)

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

-- The spine stack is a stack of heap addresses
type TiStack = [Addr]

type TiDump = [TiStack]
initialTidump = []

data Node
    = NAp Addr Addr                   -- ^ Application
    | NSupercomb Name [Name] CoreExpr -- ^ Supercombinator
    | NNum Int                        -- ^ Number
    | NInd Addr                       -- ^ Indirection
    | NPrim Name Primitive            -- ^ Primitive
    deriving (Show)

type TiHeap = Heap Node

data Primitive
    = Neg
    | Add
    | Sub
    | Mul
    | Div
    deriving (Show)

type TiStats = Int

type TiGlobals = H.HashMap Name Addr

data TiState = TiState
    { _stack   :: TiStack
    , _dump    :: TiDump
    , _heap    :: TiHeap
    , _globals :: TiGlobals
    , _stats   :: TiStats
    }
makeLenses ''TiState

-- primitives :: H.HashMap Name Primitive
primitives :: [(Name, Primitive)]
primitives =
    [ ("negate", Neg)
    , ("+", Add), ("-", Sub)
    , ("*", Mul), ("/", Div)
    ]

tiStatInitial :: TiStats
tiStatIncSteps :: TiStats -> TiStats
tiStatGetSteps :: TiStats -> Int

tiStatInitial = 0
tiStatIncSteps = (+1)
tiStatGetSteps = id

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats statsFun state = state & stats %~ statsFun

-- | create the initial state of the machine from the program
compile :: CoreProgram -> TiState
compile program =
    TiState initialStack initialTidump initialHeap globals tiStatInitial
    where
        scDefs = program ++ preludeDefs ++ extraPreludeDefs
        (initialHeap, globals) = buildInitialHeap scDefs

        addressOfMain = fromMaybe (error "main is not defined") $ globals ^? ix "main"
        initialStack = [addressOfMain]

extraPreludeDefs = []

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = (heap2, H.fromList $ scAddrs ++ primAddrs)
    where (heap1, scAddrs) = mapAccumL allocateSc U.initial scDefs
          (heap2, primAddrs) = mapAccumL allocatePrim heap1 primitives

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = U.alloc heap $ NSupercomb name args body

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = U.alloc heap $ NPrim name prim

primStep :: TiState -> Primitive -> TiState
primStep state Neg = primNeg state
primStep state Add = primArith state (+)
primStep state Sub = primArith state (-)
primStep state Mul = primArith state (*)
primStep state Div = primArith state div

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state f
    | length stack' > 3 = error $ "More than one argument to arith prim"
    | length stack' < 3 = error $ "No arguments to arith prim"
    | not (isDataNode arg1) = state & stack .~ [arg1Addr]
                                    & dump  %~ ([rootNode]:)
    | not (isDataNode arg2) = state & stack .~ [arg2Addr]
                                    & dump  %~ ([rootNode]:)
    | otherwise = state & stack %~ drop 2
                        &  heap %~ U.update rootNode (NNum $ m `f` n)
    where stack' = state^.stack
          heap' = state^.heap
          rootNode = stack' !! 2
          arg1Addr = head $ getargs heap' stack'
          arg2Addr = head $ tail $ getargs heap' stack'
          arg1 = U.lookup arg1Addr heap'
          arg2 = U.lookup arg2Addr heap'
          NNum m = arg1
          NNum n = arg2

primNeg :: TiState -> TiState
primNeg state
    | length stack' > 2 = error $ "More than one argument to neg"
    | length stack' < 2 = error $ "No arguments to neg"
    | isDataNode arg = state & stack %~ tail
                             & heap  %~ U.update (stack' !! 1) (NNum (-n))
    | otherwise = state & stack .~ [argAddr]
                        & dump  %~ ([stack' !! 1]:)
    where stack' = state^.stack
          heap' = state^.heap
          argAddr = head $ getargs heap' stack'
          arg = U.lookup argAddr heap'
          NNum n = arg

eval :: TiState -> [TiState]
eval state = state:restStates where
    restStates | tiFinal state = []
                | otherwise = eval nextState
    nextState = doAdmin $ step state

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

tiFinal :: TiState -> Bool
tiFinal state = case state^.stack of
    [soleAddr] -> dataNode && emptyDump
        where dataNode = isDataNode $ U.lookup soleAddr (state^.heap)
              emptyDump = null $ state^.dump
    [] -> error "Empty stack!"
    _ -> False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode node = False

step :: TiState -> TiState
step state = dispatch $ U.lookup (head stack') (state^.heap) where
    stack' = state^.stack
    dispatch (NNum n) = numStep state n
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    --         a :s    d    h[a:NInd a1]    f
    --     ==> a1:s    d    h               f
    dispatch (NInd a1) = state & stack .~ a1:(tail stack') -- TODO update stats?
    -- U.free heap (head stack)
    dispatch (NPrim _ prim) = primStep state prim

numStep :: TiState -> Int -> TiState
numStep state n
    | state^.stack^.to length == 1 && not (null $ state^.dump)
    = state & stack .~ head (state^.dump)
            & dump  %~ tail
numStep _ _ = error "Number applied as a function!"

-- TODO use lens
apStep :: TiState -> Addr -> Addr -> TiState
apStep state a1 a2 = case state^.heap^.to (U.lookup a2) of
    NInd a2' -> state & heap  %~ U.update (head (state^.stack)) (NAp a1 a2')
    _        -> state & stack %~ (a1:)

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
scStep state _ argNames body = state & stack .~ newStack
                                            & heap  .~ newHeap
    where
    newStack = drop (length argNames) (state^.stack)
    argBindings = zip argNames $ getargs (state^.heap) (state^.stack)
    env = H.union (H.fromList argBindings) (state^.globals)
    bodyAddr = head newStack
    newHeap = instantiateAndUpdate body bodyAddr (state^.heap) env

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:stack) = map getArg stack where
    getArg addr = arg where (NAp fun arg) = U.lookup addr heap

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
instantiateAndUpdate (ENum n) updAddr heap _ = U.update updAddr (NNum n) heap
-- replace the old application with the result of instantiation
instantiateAndUpdate (EAp e1 e2) updAddr heap env =
    U.update updAddr (NAp a1 a2) heap2
    where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env
instantiateAndUpdate ev@(EVar v) updAddr heap env =
    U.update updAddr (NInd $ H.lookupDefault (error $ "Undefined name " ++ show v) v env) heap
instantiateAndUpdate (EConstr tag arity) updAddr heap env = error "Not yet!"
instantiateAndUpdate (ELet isrec defs body) updAddr heap env =
    instantiateAndUpdateLet isrec defs body updAddr heap env
instantiateAndUpdate (ECase e alts) updAddr heap env = error "Not yet!"

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateAndUpdateLet isrec defs body updAddr heap env = result where
    (resultHeap, resultEnv) = foldl' (\(heap', env') (a, expr) ->
        let thisEnv = case isrec of
                Recursive -> resultEnv
                NonRecursive -> env'
            (heap'', addr) = (instantiate expr heap' thisEnv)
            env'' = H.insert a addr env'
        in (heap'', env'')) (heap, env) defs
    result = instantiateAndUpdate body updAddr resultHeap resultEnv

instantiate :: CoreExpr -- ^ body of supercombinator
            -> TiHeap   -- ^ heap before instantiation
            -> H.HashMap Name Addr -- ^ association of names to addresses
            -- | heap after instantiation and address of root of instance
            -> (TiHeap, Addr)
instantiate (ENum n) heap _ = U.alloc heap $ NNum n
instantiate (EAp e1 e2) heap env = U.alloc heap2 $ NAp a1 a2 where
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
showState state = showStack (state^.heap) (state^.stack) <> line

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
