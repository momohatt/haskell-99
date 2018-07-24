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
myLength (_ : xl) = (myLength xl) + 1

-- 5. Reverse a list.

myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x : xl) = myReverse xl ++ [x]

-- 6. Find out whether a list is a palindrome.

isPalindrome :: (Eq a) => [a] -> Bool
isPalindrome l =
    l == (myReverse l)


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
    | (x == y) = compress xl
    | (x /= y) = x : (compress xl)

-- 9. Pack consecutive duplicates of list elements into sublists.

pack :: (Eq a) => [a] -> [[a]]
pack []  = []
pack [x] = [[x]]
pack (x : xl @ (y : _))
    | (x == y)  = (x : z) : zl
    | otherwise = [x] : (z : zl)
    where (z : zl) = pack xl

-- 10. Run-length encoding of a list.

encode :: (Eq a) => [a] -> [(Int, a)]
encode [] = []
encode l = map (\x -> ((length x), (head x))) (pack l)

