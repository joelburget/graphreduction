module Step where

import Control.Lens
import qualified Data.HashMap.Lazy as H

import GraphReduction
import Instantiate
import qualified Utils as U
import Utils (Addr, Heap)

-- TODO use prism?
isDataNode :: Node -> Bool
isDataNode (NNum n)    = True
isDataNode (NData _ _) = True
isDataNode node = False

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap (sc:stack) = map getArg stack where
    getArg addr = arg where (NAp _ arg) = U.lookup addr heap

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
          args = getargs heap' stack'
          arg1Addr = head args
          arg2Addr = head $ tail args
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

unDump :: TiState -> TiState
unDump state
    | state^.stack^.to length == 1 && not (null $ state^.dump)
    = state & stack .~ head (state^.dump)
            & dump  %~ tail
unDump _ = error "Data applied as a function!"

step :: TiState -> TiState
step state = dispatch $ U.lookup (head (state^.stack)) (state^.heap) where
    dispatch (NNum _) = unDump state
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSupercomb sc args body) = scStep state sc args body
    --         a :s    d    h[a:NInd a1]    f
    --     ==> a1:s    d    h               f
    dispatch (NInd a1) = state & stack._head .~ a1 -- TODO update stats?
    dispatch (NPrim _ prim) = primStep state prim
    dispatch (NData _ _) = unDump state

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

tiFinal :: TiState -> Bool
tiFinal state = case state^.stack of
    [] -> True
    [soleAddr] -> dataNode && emptyDump
        where dataNode = isDataNode $ U.lookup soleAddr (state^.heap)
              emptyDump = null $ state^.dump
    _ -> False
