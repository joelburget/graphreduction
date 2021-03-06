{-# LANGUAGE TemplateHaskell #-}
module Machine.Internal.Heap where

import Control.Lens
import Data.IntMap.Lazy as M hiding (size, map)
import Data.Maybe (fromMaybe)
import Prelude hiding (lookup, map)

-- | The number of objects in the heap, list of unused addresses, map from
-- addresses to objects
data PolyHeap a = PolyHeap
    { _size   :: Int
    , _unused :: [Int]
    , _map    :: IntMap a
    }
makeLenses ''PolyHeap

instance Show a => Show (PolyHeap a) where
    show heap = "PolyHeap { size = " ++ show (heap^.size) ++ ", map = " ++ show (heap^.map) ++ "}"

type Addr = Int

-- | An initialized empty heap
initial :: PolyHeap a
initial = PolyHeap 0 [1..] empty

-- | Given a heap and an object, alloc returns a new heap and an address.
-- The new heap is exactly the same as the old one, except that the
-- specified object is found at the address returned.
alloc :: a -> PolyHeap a -> (PolyHeap a, Addr)
alloc n (PolyHeap size (next:free) cts) =
    (PolyHeap (size + 1) free (insert next n cts), next)

-- | Returns a new heap in which the address is now associated with the
-- object
update :: Addr -> a -> PolyHeap a -> PolyHeap a
update a n heap = heap & map %~ adjust (const n) a

-- | Returns a new heap with the specified object removed
free :: Addr -> PolyHeap a -> PolyHeap a
free a (PolyHeap size free cts) = PolyHeap (size - 1) (a:free) (delete a cts)

-- | Return the object associated with the address
lookup :: Addr -> PolyHeap a -> a
lookup a heap = fromMaybe err (M.lookup a (heap^.map))
    where err = error $ "can't find node " ++ show a ++ " in heap"

-- | The addresses of all the objects in the heap
addresses :: PolyHeap a -> [Addr]
addresses heap = heap^.map^.to keys

-- | An address guaranteed to differ from every address returned by alloc
null :: Addr
null = 0

-- | Whether the address is the distinguished value null
isnull :: Addr -> Bool
isnull = (==0)
