import qualified System.Random as R
import Data.Either
import qualified Data.List as L

-- 1. Find the last element of a list.

myLast :: [a] -> a
myLast []        = error "cannot apply myLast to an empty list"
myLast [x]       = x
myLast (_ : xl) = myLast xl

-- 2. Find the last but one element of a list.

myButLast :: [a] -> a
myButLast []       = error "list length must be greater than 2"
myButLast [x]      = error "list length must be greater than 2"
myButLast [x, y]   = x
myButLast (_ : xl) = myButLast xl

-- 3. Find the K'th element of a list. The first element in the list is number 1.

elementAt :: [a] -> Int -> a
elementAt [] _       = error "Index out of bounds"
elementAt (x : xl) n
    | n < 1     = error "Index out of bounds"
    | n == 1    = x
    | otherwise = elementAt xl (n - 1)

-- 4. Find the number of elements of a list.

myLength :: [a] -> Int
myLength []       = 0
myLength (_ : xl) = myLength xl + 1

-- 5. Reverse a list.

myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x : xl) = myReverse xl ++ [x]

-- 6. Find out whether a list is a palindrome.

isPalindrome :: (Eq a) => [a] -> Bool
isPalindrome l =
    l == myReverse l


-- 7. Flatten a nested list structure.

data NestedList a = Elem a | List [NestedList a]

flatten :: NestedList a -> [a]
flatten (Elem n)        = [n]
flatten (List [])       = []
flatten (List (x : xl)) = flatten x ++ flatten (List xl)

-- 8. Eliminate consecutive duplicates of list elements.

compress :: (Eq a) => [a] -> [a]
compress []           = []
compress [x]          = [x]
compress (x : xl @ (y : _))
    | x == y    = compress xl
    | otherwise = x : compress xl

-- 9. Pack consecutive duplicates of list elements into sublists.

pack :: (Eq a) => [a] -> [[a]]
pack []  = []
pack [x] = [[x]]
pack (x : xl @ (y : _))
    | x == y    = (x : z) : zl
    | otherwise = [x] : (z : zl)
    where (z : zl) = pack xl

-- 10. Run-length encoding of a list.

encode :: (Eq a) => [a] -> [(Int, a)]
encode [] = []
encode l = map (\x -> (length x, head x)) (pack l)

-- 11. Modified run-length encoding.

data ListElem a = Single a | Multiple Int a
    deriving Show

encodeModified :: Eq a => [a] -> [ListElem a]
encodeModified xl =
    reverse (map toListElem (encode xl))
        where toListElem (1, y) = Single y
              toListElem (x, y) = Multiple x y

-- 12. Decode a run-length encoded list.
decodeModified :: Eq a => [ListElem a] -> [a]
decodeModified =
    foldr helper []
        where helper (Single x) acc     = x:acc
              helper (Multiple n x) acc = replicate n x ++ acc

-- 13. Run-length encoding of a list (direct solution).

encodeDirect :: Eq a => [a] -> [ListElem a]
encodeDirect xl =
    reverse (map toListElem (encodeHelper_ [] xl))
        where toListElem (1, y) = Single y
              toListElem (x, y) = Multiple x y
encodeHelper_ xl []     = xl
encodeHelper_ [] (y:ys) = encodeHelper_ [(1, y)] ys
encodeHelper_ xl@((n, x):xs) (y:ys)
    | x == y = encodeHelper_ ((n + 1, x):xs) ys
    | otherwise = encodeHelper_ ((1, y):xl) ys

-- 14. Duplicate the elements of a list.
dupli :: [a] -> [a]
dupli =
    concatMap (\x -> [x, x])

-- 15. Replicate the elements of a list a given number of times.
repli :: [a] -> Int -> [a]
repli xl n =
    concatMap (replicate n) xl

-- 16. Drop every N'th element from a list.
dropEvery :: [a] -> Int -> [a]
dropEvery xl n =
    let xnl = zip [1..(length xl)] xl
     in map snd (filter (\(i, _) -> i `mod` n /= 0) xnl)

-- 17. Split a list into two parts; the length of the first part is given.
split :: [a] -> Int -> ([a], [a])
split xl n =
    (take' xl n, remove xl n)
        where take' [] n = []
              take' (x:xs) n
                | n > 0     = x : take' xs (n - 1)
                | otherwise = []
              remove [] n = []
              remove (x:xs) n
                | n > 0     = remove xs (n - 1)
                | otherwise = x : remove xs 0

-- 18. Extract a slice from a list.
slice :: [a] -> Int -> Int -> [a]
slice xl begin end =
    let xnl = zip [1..(length xl)] xl
     in map snd (filter (\(i, _) -> i >= begin && i <= end) xnl)

-- 19. Rotate a list N places to the left.
rotate :: [a] -> Int -> [a]
rotate xl n =
    let (l1, l2) = split xl m in l2 ++ l1
        where m = let m = n `mod` length xl in
                      if m < 0 then length xl + m else m

-- 20. Remove the K'th element from a list.
removeAt :: Int -> [a] -> (a, [a])
removeAt n xl =
    let (l1, l2) = split xl n
     in (last l1, init l1 ++ l2)

-- 21. Insert an element at a given position into a list.
insertAt :: a -> [a] -> Int -> [a]
insertAt x [] 1 = [x]
insertAt x [] n = error "Index out of bounds"
insertAt x yl@(y:ys) n
  | n == 1    = x : yl
  | n > 1     = y : insertAt x ys (n - 1)
  | otherwise = error "Index out of bounds"

-- 22. Create a list containing all integers within a given range.<Paste>
range :: Int -> Int -> [Int]
range n m = [n..m]

-- 23. Extract a given number of randomly selected elements from a list.
rndSelect :: [a] -> Int -> IO [a]
rndSelect [] _ = return []
rndSelect l n | n <= 0    = return []
              | otherwise = do
                  gen <- R.getStdGen
                  return $ take n [ l !! x | x <- R.randomRs (0, length l - 1) gen]

-- 24. Lotto: Draw N different random numbers from the set 1..M.
diffSelect :: Int -> Int -> IO [Int]
diffSelect n m | n < 0     = error "invalid input"
               | otherwise = take n . R.randomRs (1, m) <$> R.getStdGen

-- 25. Generate a random permutation of the elements of a list.
dropNth :: Int -> [a] -> [a]
dropNth n l
  | n < 0         = error "invalid input"
  | length l <= n = error "list too short"
  | n == 0        = tail l
  | otherwise     = head l : dropNth (n - 1) (tail l)

rndPermu :: [a] -> IO [a]
rndPermu [] = return []
rndPermu l = do
    n <- head . R.randomRs (0, length l - 1) <$> R.getStdGen
    ((l !! n) :) <$> rndPermu (dropNth n l)

-- 26. Generate the combinations of K distinct objects chosen from the N elements of a list
combinations :: Int -> [a] -> [[a]]
combinations 0 _      = []
combinations n []     = []
combinations 1 l      = map (: []) l
combinations n (x:xs) =
    map (x :) (combinations (n - 1) xs) ++ combinations n xs

-- 27. Group the elements of a set into disjoint subsets.
group :: Eq a => [Int] -> [a] -> [[[a]]]
group [] _ = []
group [n] xs = [combinations n xs]
group (n:ns) xs =
    let chosen = combinations n xs in
        concatMap (\p ->
            let left = filter (`notElem` p) xs in
                map (\q -> p : q) $ group ns left) chosen

-- 28. Sorting a list of lists according to length of sublists
-- a) Sort by length
lsort :: [[a]] -> [[a]]
lsort l =
    map snd $ L.sortOn fst $ map (\x -> (length x, x)) l

-- b) Sort by frequency
assoc :: Eq a => [(a, Int)] -> a -> Int
assoc [] _    = 0
assoc (x:xs) n | fst x == n = snd x
               | otherwise  = assoc xs n

lfsort :: [[a]] -> [[a]]
lfsort l =
    let freq = map (\x -> (head x, length x)) $ L.group $ L.sort $ map length l in
        map snd $ L.sortOn fst $ map (\x -> (assoc freq $ length x, x)) l
