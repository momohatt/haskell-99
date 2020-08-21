-- Dependently-typed Binary Tree

module BinTree

data Tree : (n : Nat) -> (a : Type) -> Type where
  Empty  : Tree Z a
  Branch : a -> Tree n a -> Tree m a -> Tree (S (n + m)) a

leaf : a -> Tree 1 a
leaf x = Branch x Empty Empty

tree1 : Tree 7 Char
tree1 = Branch 'a' (Branch 'b' (leaf 'd')
                               (leaf 'e'))
                   (Branch 'c' Empty
                               (Branch 'f' (leaf 'g')
                                           Empty))

tree2 : Tree 1 Char
tree2 = Branch 'a' Empty Empty

tree3 : Tree 0 a
tree3 = Empty

tree4 : Tree 4 Int
tree4 = Branch 1 (Branch 2 Empty (Branch 4 Empty Empty))
                 (Branch 2 Empty Empty)

-- 55.
data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

helpEven : (j : Nat) -> Parity (S j + S j) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p

helpOdd : (j : Nat) -> Parity (S (S (j + S j))) -> Parity (S (S (S (j + j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even = helpEven j (Even {n = S j})
  parity (S (S (S (j + j)))) | Odd  = helpOdd j (Odd {n = S j})

cbalTree : (n : Nat) -> List (Tree n Int)
cbalTree Z     = [Empty]
cbalTree (S n) with (parity n)
  cbalTree (S (m + m))     | Even =
    [Branch 0 l r | l <- cbalTree m, r <- cbalTree m]
  cbalTree (S (S (m + m))) | Odd  =
    [Branch 0 l r | l <- cbalTree (S m), r <- cbalTree m] ++
    rewrite plusSuccRightSucc m m in
    [Branch 0 l r | l <- cbalTree m, r <- cbalTree (S m)]
