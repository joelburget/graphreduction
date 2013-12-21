{-# LANGUAGE TemplateHaskell #-}
module Utils where

import Control.Lens
import Data.IntMap.Lazy as M hiding (size, map)
import Data.List (mapAccumL)
import Prelude hiding (lookup, map)

-- | The number of objects in the heap, list of unused addresses, map from
-- addresses to objects
data Heap a = Heap
    { _size   :: Int
    , _unused :: [Int]
    , _map    :: IntMap a
    }
makeLenses ''Heap

type Addr = Int

-- | An initialized empty heap
initial :: Heap a
initial = Heap 0 [1..] empty

-- | Given a heap and an object, hAlloc returns a new heap and an address.
-- The new heap is exactly the same as the old one, except that the
-- specified object is found at the address returned.
alloc :: Heap a -> a -> (Heap a, Addr)
alloc (Heap size (next:free) cts) n =
    (Heap (size + 1) free (insert next n cts), next)

-- | Returns a new heap in which the address is now associated with the
-- object
update :: Addr -> a -> Heap a -> Heap a
update a n (Heap size free cts) = (Heap size free (adjust (const n) a cts))

-- | Returns a new heap with the specified object removed
free :: Heap a -> Addr -> Heap a
free (Heap size free cts) a = (Heap (size - 1) (a:free) (delete a cts))

-- | Return the object associated with the address
lookup :: Addr -> Heap a -> a
lookup a heap = aLookup (heap^.map) a $
    error $ "can't find node " ++ show a ++ " in heap"

-- | Lookup list key default
aLookup :: IntMap a -> Addr -> a -> a
aLookup heap a def = maybe def id (M.lookup a heap)

-- | The addresses of all the objects in the heap
addresses :: Heap a -> [Addr]
addresses heap = heap^.map^.to keys

-- | An address guaranteed to differ from every address returned by hAlloc
null :: Addr
null = 0

-- | Whether the address is the distinguished value null
isnull :: Addr -> Bool
isnull = (==0)
