data Tree a = Empty | Branch a (Tree a) (Tree a)
              deriving (Show, Eq)

-- 55. Construct completely balanced binary trees
cbalTree :: Int -> [Tree Char]
cbalTree 0 = [Empty]
cbalTree n = let (q, r) = (n - 1) `quotRem` 2
    in [Branch 'x' left right | i     <- [q .. q + r],
                                left  <- cbalTree i,
                                right <- cbalTree (n - i - 1)]

-- 56. Symmetric binary trees
mirror :: Eq a => Tree a -> Tree a -> Bool
mirror Empty Empty = True
mirror (Branch _ t1 t2) (Branch _ s1 s2) = mirror t1 s2 && mirror t2 s1
mirror _ _ = False

symmetric :: Eq a => Tree a -> Bool
symmetric Empty = True
symmetric (Branch _ t1 t2) = mirror t1 t2

-- 57. Construct binary search trees
add :: Ord a => Tree a -> a -> Tree a
add Empty x = Branch x Empty Empty
add (Branch b c1 c2) x =
  if x <= b then Branch b (add c1 x) c2
            else Branch b c1 (add c2 x)

construct :: Ord a => [a] -> Tree a
construct l = foldl add Empty l

-- 58. Construct all symmetric, completely balanced binary trees with a given number of nodes
symCbalTrees :: Int -> [Tree Char]
symCbalTrees =
  filter symmetric . cbalTree

-- 59. Construct height-balanced binary trees
hbalTree :: a -> Int -> [Tree a]
hbalTree x n
  | n < 0     = error "Invalid height"
  | n == 0    = [Empty]
  | n == 1    = [Branch x Empty Empty]
  | otherwise = [Branch x t1 t2 | t1 <- hbalTree x (n - 1), t2 <- hbalTree x (n - 1)]
             ++ [Branch x t1 t2 | t1 <- hbalTree x (n - 1), t2 <- hbalTree x (n - 2)]
             ++ [Branch x t1 t2 | t1 <- hbalTree x (n - 2), t2 <- hbalTree x (n - 1)]

-- 60. Construct height-balanced binary trees with a given number of nodes
minNodes :: Int -> Int
minNodes n
  | n < 0     = error "Invalid argument"
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = 1 + minNodes (n - 1) + minNodes (n - 2)

maxHeight :: Int -> Int
maxHeight n = maxHeight_ n 0
  where maxHeight_ n k = if minNodes k <= n then maxHeight_ n (k + 1)
                                            else k - 1

minHeight :: Int -> Int
minHeight n = minHeight_ n 0 1
  where minHeight_ n k k2 = if n <= k2 - 1 then k
                                           else minHeight_ n (k + 1) (2 * k2)

numNodes :: Tree a -> Int
numNodes Empty = 0
numNodes (Branch _ t1 t2) = 1 + numNodes t1 + numNodes t2

hbalTreeNodes :: a -> Int -> [Tree a]
hbalTreeNodes x n =
  hbalTreeNodes_ x n (minHeight n) (maxHeight n)
  where hbalTreeNodes_ x n i m
          | i <= m    = filter ((== n) . numNodes) (hbalTree x i) ++ hbalTreeNodes_ x n (i + 1) m
          | otherwise = []

-- 61. Count the leaves of a binary tree
tree4 = Branch 1 (Branch 2 Empty (Branch 4 Empty Empty))
                 (Branch 2 Empty Empty)

countLeaves :: Tree a -> Int
countLeaves Empty = 0
countLeaves (Branch _ Empty Empty) = 1
countLeaves (Branch _ t1 t2) = countLeaves t1 + countLeaves t2

-- 61 A. Collect the leaves of a binary tree in a list
leaves :: Tree a -> [a]
leaves Empty = []
leaves (Branch x Empty Empty) = [x]
leaves (Branch _ t1 t2) = leaves t1 ++ leaves t2

-- 62. Collect the internal nodes of a binary tree in a list<Paste>
internals :: Tree a -> [a]
internals Empty = []
internals (Branch _ Empty Empty) = []
internals (Branch x t1 t2) = [x] ++ internals t1 ++ internals t2

-- 62 A. Collect the nodes at a given level in a list
atLevel :: Tree a -> Int -> [a]
atLevel t n
  | n < 0     = error "Invalid argument"
  | otherwise =
    case t of
      Empty -> []
      Branch x t1 t2
        | n == 0 -> []
        | n == 1 -> [x]
        | n >= 2 -> atLevel t1 (n - 1) ++ atLevel t2 (n - 1)
