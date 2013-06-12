module Utils where

import Data.IntMap.Lazy
import Data.List (mapAccumL)
import Prelude hiding (lookup)

-- | The number of objects in the heap, list of unused addresses, map from
-- addresses to objects
type Heap a = (Int, [Int], IntMap a)
type Addr = Int

-- | An initialized empty heap
hInitial :: Heap a
hInitial = (0, [1..], empty)

-- | Given a heap and an object, hAlloc returns a new heap and an address.
-- The new heap is exactly the same as the old one, except that the
-- specified object is found at the address returned.
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = ((size + 1, free, insert next n cts), next)

-- | Returns a new heap in which the address is now associated with the
-- object
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, adjust (const n) a cts)

-- | Returns a new heap with the specified object removed
hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size - 1, a:free, delete a cts)

-- | Return the object associated with the address
hLookup :: Heap a -> Addr -> a
hLookup (_, _, cts) a = aLookup cts a (error $ "can't find node " ++ show a ++ " in heap")
-- hLookup (_, _, cts) a = complain $ lookup a cts where
--     complain = maybe (error $ "can't find node " ++ show a ++ " in heap") id

-- | Lookup list key default
aLookup :: IntMap a -> Addr -> a -> a
aLookup map a def = maybe def id (lookup a map)

-- | The addresses of all the objects in the heap
hAddresses :: Heap a -> [Addr]
hAddresses (_, _, cts) = keys cts

-- | The number of objects in the heap
hSize :: Heap a -> Int
hSize (size, _, _) = size

-- | An address guaranteed to differ from every address returned by hAlloc
hNull :: Addr
hNull = 0

-- | Whether the address is the distinguished value null
hIsnull :: Addr -> Bool
hIsnull = (==0)
