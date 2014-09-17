{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Machine.Internal.Data where

import Control.Lens
import qualified Data.HashMap.Lazy as H
import Data.List (mapAccumL)
import Data.Text hiding (length, intersperse, last, map, head, zip, drop,
                        mapAccumL, foldl', tail, null, concat, foldl, foldl1,
                        dropWhile, find)

import qualified Machine.Internal.Heap as U
import Machine.Internal.Heap (Addr, Heap)


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
        [CaseAlt a]           -- alternatives
    | ELam [a] (Expr a)     -- ^ Lambda abstraction
    deriving (Show, Eq)

type CoreExpr = Expr Name
type Name = Text

-- | Is this let recursive?
data IsRec = Recursive | NonRecursive deriving (Show, Eq)

-- | Alternative - containing a tag, list of bound variables, and
-- expression to the right of the arrow
type CaseAlt a = (Int, [a], Expr a)
type CoreCaseAlt = CaseAlt Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

type Program a = [ScDefn a]
type CoreProgram = Program Name

data MarkState = Done       -- ^ Finished garbage collecting
               | Visits Int -- ^ Visited n times this garbage collection
               deriving (Show, Eq)

data Node
    = NAp Addr Addr                   -- ^ Application
    | NSupercomb Name [Name] CoreExpr -- ^ Supercombinator
    | NNum Int                        -- ^ Number
    | NInd Addr                       -- ^ Indirection
    | NPrim Name Primitive            -- ^ Primitive
    | NData Int [Addr]                -- ^ Tag, list of components
    | NMarked MarkState Node          -- ^ Marked node
    deriving (Show, Eq)

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
    deriving (Show, Eq)

-- The spine stack is a stack of heap addresses
type TiStack = [Addr]

type TiDump = [TiStack]
initialTidump :: TiDump
initialTidump = []

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

data PreludeAndPrims = PreludeAndPrims
    { prelude :: CoreProgram
    , prims :: [(Name, Primitive)]
    }

tiStatInitial :: TiStats
tiStatInitial = 0


buildInitialHeap :: [CoreScDefn] -> [(Name, Primitive)] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs prims = (heap2, H.fromList $ scAddrs ++ primAddrs)
    where (heap1, scAddrs)   = mapAccumL allocateSc U.initial scDefs
          (heap2, primAddrs) = mapAccumL allocatePrim heap1 prims

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NSupercomb name args body) heap

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NPrim name prim) heap
