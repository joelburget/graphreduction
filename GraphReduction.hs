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

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

type Program a = [ScDefn a]
type CoreProgram = Program Name

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
    | NData Int [Addr]                -- ^ Tag, list of components
    deriving (Show)

type TiHeap = Heap Node

data Primitive
    = Neg
    | Add
    | Sub
    | Mul
    | Div
    | PrimConstr Int Int
    | If
    | Greater
    | GreaterEq
    | Less
    | LessEq
    | Eq
    | NotEq
    | CasePair
    | Abort
    | CaseList
    | Print
    | Stop
    deriving (Show)

type TiOutput = [Int]
type TiStats = Int
type TiGlobals = H.HashMap Name Addr

data TiState = TiState
    { _output  :: TiOutput
    , _stack   :: TiStack
    , _dump    :: TiDump
    , _heap    :: TiHeap
    , _globals :: TiGlobals
    , _stats   :: TiStats
    } deriving (Show)
makeLenses ''TiState

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
    TiState [] initialStack initialTidump initialHeap globals tiStatInitial
    where
        scDefs = preludeDefs ++ extraPreludeDefs ++ program
        (initialHeap, globals) = buildInitialHeap scDefs

        addressOfMain = fromMaybe (error "main is not defined") $ globals ^? ix "main"
        initialStack = [addressOfMain]

extraPreludeDefs = []

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = (heap2, H.fromList $ scAddrs ++ primAddrs)
    where (heap1, scAddrs)   = mapAccumL allocateSc U.initial scDefs
          (heap2, primAddrs) = mapAccumL allocatePrim heap1 primitives

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NSupercomb name args body) heap

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NPrim name prim) heap

primStep :: TiState -> Primitive -> TiState
primStep state Neg = primNeg state
primStep state Add = primArith state (+)
primStep state Sub = primArith state (-)
primStep state Mul = primArith state (*)
primStep state Div = primArith state div
primStep state If  = primIf state
primStep state (PrimConstr tag arity) = primConstr state tag arity
primStep state Greater   = primComp state (>)
primStep state GreaterEq = primComp state (>=)
primStep state Less      = primComp state (<)
primStep state LessEq    = primComp state (<=)
primStep state Eq        = primComp state (==)
primStep state NotEq     = primComp state (/=)
primStep state CasePair = primCasePair state
primStep state Abort = error "Abort!"
primStep state CaseList = primCaseList state
primStep state Print = primPrint state
primStep state Stop = primStop state

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state f = primDyadic state (\(NNum x) (NNum y) -> (NNum (f x y)))

primComp :: TiState -> (Int -> Int -> Bool) -> TiState
primComp state f = primDyadic state $ \(NNum x) (NNum y) ->
    (NData (if (f x y) then 2 else 1) [])

primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic state f
    | length stack' > 3 = error $ "More than two arguments to dyadic prim"
    | length stack' < 3 = error $ "Less than two arguments to dyadic prim"
    | not (isDataNode m) = state & stack .~ [arg1Addr]
                                 & dump  %~ ([rootNode]:)
    | not (isDataNode n) = state & stack .~ [arg2Addr]
                                 & dump  %~ ([rootNode]:)
    | otherwise = state & stack %~ drop 2
                        &  heap %~ U.update rootNode (m `f` n)
    where stack' = state^.stack
          heap'  = state^.heap
          rootNode = stack' !! 2
          arg1Addr = head $ getargs heap' stack'
          arg2Addr = head $ tail $ getargs heap' stack'
          m = U.lookup arg1Addr heap'
          n = U.lookup arg2Addr heap'

primNeg :: TiState -> TiState
primNeg state
    | length stack' > 2 = error $ "More than one argument to neg"
    | length stack' < 2 = error $ "No arguments to neg"
    | isDataNode arg = state & stack %~ tail
                             & heap  %~ U.update (stack' !! 1) (NNum (-n))
    | otherwise = state & stack .~ [argAddr]
                        & dump  %~ ([stack' !! 1]:)
    where stack' = state^.stack
          heap'  = state^.heap
          argAddr = head $ getargs heap' stack'
          arg = U.lookup argAddr heap'
          NNum n = arg

followIndirection :: Node -> TiHeap -> Node
followIndirection (NInd addr) heap = followIndirection (U.lookup addr heap) heap
followIndirection node        _    = node

--         a0:a1:...:an:s    d    h[a0:NSupercomb[x1, ..., xn] body]    f
--     ==>           ar:s    d    h'[an:NInd ar]                        f

--     a0:s d h[ a0:NPrim _ If
--               a1:NData _ ] f
-- ==>
primIf :: TiState -> TiState
primIf state
    | length stack' < 4 = error $ "Less than three arguments to if"
    | length stack' > 4 = error $ "More than three arguments to if"
    | isDataNode bool = state & stack .~ newStack
                              & heap  .~ newHeap
    | otherwise = state & stack .~ [boolAddr]
                        & dump  %~ ([stack' !! 3]:)
    where stack' = state^.stack
          heap'  = state^.heap
          args = getargs heap' stack'
          boolAddr = head args
          -- TODO - do we need followIndirection?
          bool = followIndirection (U.lookup boolAddr heap') heap'

          -- isDataNode case
          NData t _ = bool
          branchAddr = if t == 1 then args !! 2 else args !! 1
          newHeap = U.update (stack' !! 3) (NInd branchAddr) heap'
          newStack = drop 3 stack'

primCasePair :: TiState -> TiState
primCasePair state
    | length stack' < 3 = error $ "Less than two arguments to casePair"
    | length stack' > 3 = error $ "More than two arguments to casePair"
    | isDataNode pair = state & stack .~ newStack
                              & heap  .~ newHeap
    | otherwise = state & stack .~ [pairAddr]
                        & dump  %~ ([stack' !! 2]:)
    where stack' = state^.stack
          heap'  = state^.heap
          args = getargs heap' stack'
          pairAddr = head args
          -- TODO - do we need followIndirection?
          pair = followIndirection (U.lookup pairAddr heap') heap'

          -- isDataNode case
          -- this is disgusting
          (NData _ [aAddr, bAddr]) = pair
          fAddr = head $ tail args
          (heap'', fAppA) = U.alloc (NAp fAddr aAddr) heap'
          (heap''', newRoot) = U.alloc (NAp fAppA bAddr) heap''
          newHeap = U.update (last stack') (NInd newRoot) heap'''
          newStack = [fAddr, fAppA, newRoot]

primCaseList :: TiState -> TiState
primCaseList state
    | length stack' < 4 = error $ "Less than three arguments to caseList"
    | length stack' > 4 = error $ "More than three arguments to caseList"
    | isDataNode lst = state & stack .~ newStack
                             & heap  .~ newHeap
    | otherwise = state & stack .~ [lstAddr]
                        & dump  %~ ([stack' !! 3]:)
    where stack' = state^.stack
          heap'  = state^.heap
          args = getargs heap' stack'
          lstAddr = head args
          -- TODO - do we need followIndirection?
          lst = followIndirection (U.lookup lstAddr heap') heap'
          cnAddr = args !! 1
          ccAddr = args !! 2

          -- isDataNode case
          -- caseList Pack{1, 0}        cn cc = cn
          -- caseList (Pack{2, 2} x xs) cn cc = cc x xs
          NData tag lstParts = lst
          (newHeap, newStack) = case tag of
              -- cn
              1 -> let heap'' = U.update (last stack') (NInd cnAddr) heap'
                   in (heap'', drop 3 stack')
              -- cc x xs
              2 -> let [xAddr, xsAddr] = lstParts
                       (heap'', app1)  = U.alloc (NAp ccAddr xAddr) heap'
                       (heap''', app2) = U.alloc (NAp app1 xsAddr) heap''
                   in (heap''', [ccAddr, app1, app2])

primStop :: TiState -> TiState
primStop state = state & stack .~ []

primPrint :: TiState -> TiState
primPrint state
    | b1IsNum = state & output <>~ [n]
                      & stack .~ [b2]
    | otherwise = state & stack .~ [b1]
                        & dump .~ [[stack' !! 2]]
    where heap'  = state^.heap
          stack' = state^.stack
          [b1, b2] = getargs heap' stack'
          b1' = U.lookup b1 heap'
          b1IsNum = case b1' of
              (NNum _) -> True
              _        -> False
          NNum n = b1'

--     a0:a1:...:an:[] d h [ a0:NPrim (PrimConstr t n)    f
--                           a1:NAp a b1
--                           ...
--                           an:NAp a(n-1) bn        ]
-- ==>           an:[] d h [ an:NData t [b1,...,bn]  ]   f
primConstr :: TiState -> Int -> Int -> TiState
primConstr state tag arity
    | length stack' > (arity + 1) = error $ "Too many arguments to constructor"
    | length stack' < (arity + 1) = error $ "Not enough arguments to constructor"
    | otherwise = state & stack .~ [updAddr]
                        & heap  .~ newHeap
    where stack' = state^.stack
          heap'  = state^.heap
          -- Get the addr of a component from the address where it's applied
          -- TODO - this is ill-conceived
          componentAddrs = getargs heap' stack'
          updAddr = last stack'
          newHeap = U.update updAddr (NData tag componentAddrs) heap'
          -- (newHeap, dataAddr) = U.alloc (NData tag componentAddrs) (state^.heap)
          -- (newHeap, dataAddr) = instantiate constr (state^.heap)

eval :: TiState -> [TiState]
eval state = state:restStates where
    restStates | tiFinal state = []
               | otherwise = eval nextState
    nextState = doAdmin $ step state

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

tiFinal :: TiState -> Bool
tiFinal state = case state^.stack of
    [] -> True
    [soleAddr] -> dataNode && emptyDump
        where dataNode = isDataNode $ U.lookup soleAddr (state^.heap)
              emptyDump = null $ state^.dump
    _ -> False

isDataNode :: Node -> Bool
isDataNode (NNum n)    = True
isDataNode (NData _ _) = True
isDataNode node = False

step :: TiState -> TiState
step state = dispatch $ U.lookup (head (state^.stack)) (state^.heap) where
    dispatch (NNum _) = unDump state
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    --         a :s    d    h[a:NInd a1]    f
    --     ==> a1:s    d    h               f
    dispatch (NInd a1) = state & stack._head .~ a1 -- TODO update stats?
    -- U.free heap (head stack)
    dispatch (NPrim _ prim) = primStep state prim
    dispatch (NData _ _) = unDump state

unDump :: TiState -> TiState
unDump state
    | state^.stack^.to length == 1 && not (null $ state^.dump)
    = state & stack .~ head (state^.dump)
            & dump  %~ tail
unDump _ = error "Data applied as a function!"

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
    stack' = state^.stack
    heap'  = state^.heap
    newStack = drop (length argNames) stack'
    argBindings = zip argNames $ getargs heap' stack'
    env = H.union (H.fromList argBindings) (state^.globals)
    bodyAddr = head newStack
    newHeap = instantiateAndUpdate body bodyAddr heap' env

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:stack) = map getArg stack where
    getArg addr = arg where (NAp _ arg) = U.lookup addr heap

{-
 - Instantiate the given supercombinator body, writing over the given
 - address, if possible
 -}
instantiateAndUpdate :: CoreExpr            -- ^ body of supercombinator
                     -> Addr                -- ^ address of node to update
                     -> TiHeap              -- ^ heap before instantiation
                     -- | associate parameters to addresses
                     -> TiGlobals
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
instantiateAndUpdate (EConstr tag arity) updAddr heap env =
    instantiateAndUpdateConstr tag arity updAddr heap env
instantiateAndUpdate (ELet isrec defs body) updAddr heap env =
    instantiateAndUpdateLet isrec defs body updAddr heap env
instantiateAndUpdate (ECase e alts) updAddr heap env = error "Not yet!"

instantiateAndUpdateConstr :: Int
                           -> Int
                           -> Addr
                           -> TiHeap
                           -> TiGlobals
                           -> TiHeap
instantiateAndUpdateConstr tag arity updAddr heap env = U.update updAddr
    (NPrim "Pack" (PrimConstr tag arity)) heap

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateAndUpdateLet :: IsRec
                        -> [(Name, CoreExpr)]
                        -> CoreExpr
                        -> Addr
                        -> TiHeap
                        -> TiGlobals
                        -> TiHeap
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
instantiate (ENum n) heap _ = U.alloc (NNum n) heap
instantiate (EAp e1 e2) heap env = U.alloc (NAp a1 a2) heap2 where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env =
    (heap, H.lookupDefault (error $ "Undefined name " ++ show v) v env)
instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env
instantiate (ELet isrec defs body) heap env =
    instantiateLet isrec defs body heap env
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"

instantiateConstr tag arity heap _ = U.alloc
    (NPrim "Pack" (PrimConstr tag arity)) heap

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
showNode (NData tag components) = "NData " <> int tag

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
