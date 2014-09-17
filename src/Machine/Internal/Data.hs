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
        [(a, Expr a)]       -- definitions
        (Expr a)            -- body
    | ECase                 -- ^ Case expression
        (Expr a)            -- expression to scrutinize
        [CaseAlt a]           -- alternatives
    | ELam [a] (Expr a)     -- ^ Lambda abstraction
    deriving (Show, Eq)

type CoreExpr = Expr Name
type Name = Text

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

type Heap = Heap Node

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
type Stack = [Addr]

type Dump = [Stack]
initialdump :: Dump
initialdump = []

type Output = [Int]
type Stats = Int
type Globals = H.HashMap Name Addr

data State = State
    { _output  :: Output
    , _stack   :: Stack
    , _dump    :: Dump
    , _heap    :: Heap
    , _globals :: Globals
    , _stats   :: Stats
    } deriving (Show)
makeLenses ''State

data PreludeAndPrims = PreludeAndPrims
    { prelude :: CoreProgram
    , prims :: [(Name, Primitive)]
    }

tiStatInitial :: Stats
tiStatInitial = 0


buildInitialHeap :: [CoreScDefn] -> [(Name, Primitive)] -> (Heap, Globals)
buildInitialHeap scDefs prims = (heap2, H.fromList (scAddrs ++ primAddrs))
    where (heap1, scAddrs)   = mapAccumL allocateSc U.initial scDefs
          (heap2, primAddrs) = mapAccumL allocatePrim heap1 prims

-- allocateSc and allocatePrim have this weird signature (in the return
-- type) because they're folded with mapAccumL. We fold the heap - building
-- it up as we allocate, and accumulate a list of name-address mappings.
allocateSc :: Heap -> CoreScDefn -> (Heap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NSupercomb name args body) heap

allocatePrim :: Heap -> (Name, Primitive) -> (Heap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
    where (heap', addr) = U.alloc (NPrim name prim) heap
