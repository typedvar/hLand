module Heap
    where

import Types

-- check out the second parameter 
-- note that our addresses start from 1; 
-- 0 is reserved for the NULL address
hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), assocs) a 
    = (newHeap, next) 
    where 
        newHeap = (size + 1, free, (next, a) : assocs)

-- update the node-part of the association pointed by the 
-- address addr to newNode remove the old association
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, assocs) addr a 
    = (size, free, (addr, a) : remove assocs addr) 

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, assocs) addr 
    = (size - 1, addr:free, remove assocs addr)

hShowAddr :: Addr -> String
hShowAddr addr = "#" ++ (show addr)

aLookup :: (Eq a) => Assoc a b -> a -> b -> b
aLookup [] key def = def

aLookup ((key, value):assocs) key' def
        | key == key' = value
        | key /= key' = aLookup assocs key' def
         
aDomain :: Assoc a b -> [a]
aDomain assocs = [key | (key, value) <- assocs]

aRange :: Assoc a b -> [b]
aRange assocs = [value | (key, value) <- assocs]

aEmpty :: Assoc a b
aEmpty = []

hLookup :: Heap a -> Addr -> a
hLookup (size, free, assocs) addr = aLookup assocs addr (error ("Cannot find node " ++ hShowAddr addr ++ " in heap"))

hAssocs :: Heap a -> Assoc Addr a
hAssocs (size, free, assocs) = assocs

hAddresses :: Heap a -> [Addr]
hAddresses (size, free, assocs) = [addr | (addr, a) <- assocs]

hSize :: Heap a -> Int
hSize (size, free, assocs) = size

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull addr = addr == 0

remove :: [(Addr, a)] -> Addr -> [(Addr, a)] 
remove ((addr', n):assocs) addr
        | addr == addr' = assocs 
        | addr /= addr' = (addr', n) : remove assocs addr
        

