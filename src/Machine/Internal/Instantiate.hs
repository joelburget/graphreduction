{-# LANGUAGE OverloadedStrings #-}
module Machine.Internal.Instantiate where

import qualified Data.HashMap.Lazy as H
import Data.List (foldl')

import Machine.Internal.Data
import Machine.Internal.GC.MarkScan
import Machine.Internal.Heap (Addr)
import qualified Machine.Internal.Heap as U

{-
 - Instantiate the given supercombinator body, writing over the given
 - address, if possible
 -}
instantiateAndUpdate :: CoreExpr            -- ^ body of supercombinator
                     -> Addr                -- ^ address of node to update
                     -> Heap              -- ^ heap before instantiation
                     -- | associate parameters to addresses
                     -> Globals
                     -> Heap              -- ^ heap after instantiation
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
instantiateAndUpdate (ELet defs body) updAddr heap env =
    instantiateAndUpdateLet defs body updAddr heap env
instantiateAndUpdate (ECase e alts) updAddr heap env = error "Not yet!"

instantiateAndUpdateConstr :: Int
                           -> Int
                           -> Addr
                           -> Heap
                           -> Globals
                           -> Heap
instantiateAndUpdateConstr tag arity updAddr heap env = U.update updAddr
    (NPrim "Pack" (PrimConstr tag arity)) heap

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateAndUpdateLet :: [(Name, CoreExpr)]
                        -> CoreExpr
                        -> Addr
                        -> Heap
                        -> Globals
                        -> Heap
instantiateAndUpdateLet defs body updAddr heap env = result where
    (resultHeap, resultEnv) = foldl' (\(heap', env') (a, expr) ->
        let (heap'', addr) = instantiate expr heap' resultEnv
            env'' = H.insert a addr env'
        in (heap'', env'')) (heap, env) defs
    result = instantiateAndUpdate body updAddr resultHeap resultEnv

instantiate :: CoreExpr -- ^ body of supercombinator
            -> Heap   -- ^ heap before instantiation
            -> H.HashMap Name Addr -- ^ association of names to addresses
            -- | heap after instantiation and address of root of instance
            -> (Heap, Addr)
instantiate (ENum n) heap _ = U.alloc (NNum n) heap
instantiate (EAp e1 e2) heap env = U.alloc (NAp a1 a2) heap2 where
    (heap1, a1) = instantiate e1 heap env
    (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env =
    (heap, H.lookupDefault (error $ "Undefined name " ++ show v) v env)
instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env
instantiate (ELet defs body) heap env =
    instantiateLet defs body heap env
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"

instantiateConstr tag arity heap _ = U.alloc
    (NPrim "Pack" (PrimConstr tag arity)) heap

{-
 - Instantiate the right-hand side of each of the definitions in defs, at
 - the same time augment the environment to bind the names in defs to the
 - addresses of the newly constructed instances. Then instantiate the body
 - of the let with the augmented environment.
 -}
instantiateLet :: [(Name, CoreExpr)]
               -> CoreExpr
               -> Heap
               -> H.HashMap Name Addr
               -> (Heap, Addr)
instantiateLet defs body heap env = result where
    (resultHeap, resultEnv) = foldl' (\(heap', env') (a, expr) ->
        let (heap'', addr) = instantiate expr heap' resultEnv
            env'' = H.insert a addr env'
        in (heap'', env'')) (heap, env) defs
    result = instantiate body resultHeap resultEnv
