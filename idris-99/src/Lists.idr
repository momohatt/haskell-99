module Lists

import Data.Fin
import Data.Vect

-- 1. Find the last element of a list.

total
myLast : Vect (S n) a -> a
myLast (x :: []) = x
myLast (x :: xs@(_ :: _)) = myLast xs -- unfortunately this "as pattern" is indispensable

-- 2. Find the last but one element of a list.

total
myButLast : Vect (S (S n)) a -> a
myButLast (x :: _ :: []) = x
myButLast (x :: xs@(_ :: _ :: _)) = myButLast xs

-- 3. Find the K'th element of a list. The first element in the list is number 1.

total
elementAt : Vect n a -> Fin n -> a
elementAt (x :: _)  FZ     = x
elementAt (_ :: xs) (FS m) = elementAt xs m

-- 4. Find the number of elements of a list.
total
myLength : Vect n a -> Nat
myLength {n = n} _ = n

-- 5. Reverse a list.
total
myReverse : Vect n a -> Vect n a
myReverse {n = Z}   []        = []
myReverse {n = S n} (x :: xs) =
  rewrite trans
            (sym (plusZeroRightNeutral (S n))) -- S n -> S (n + Z)
            (plusSuccRightSucc n Z)            -- S (n + Z) -> n + S Z
  in myReverse xs ++ [x]

-- 6. Find out whether a list is a palindrome. A palindrome can be read forward or backward; e.g. (x a m a x).

-- 14. Duplicate the elements of a list.
total
dupli : Vect n a -> Vect (n + n) a
dupli {n = Z}   []        = []
dupli {n = S n} (x :: xs) =
  rewrite sym (plusSuccRightSucc (S n) n) in (x :: x :: dupli xs)

-- 15. Replicate the elements of a list a given number of times.
total
repli : Vect n a -> (m : Nat) -> Vect (n * m) a
repli {n = n} l Z     = rewrite multZeroRightZero n in []
repli {n = n} l (S m) = rewrite (multRightSuccPlus n m) in l ++ repli l m

-- 16. Drop every N'th element from a list.

-- 17. Split a list into two parts; the length of the first part is given.
total
split : Vect n a -> (m : Fin (S n)) -> (Vect (finToNat m) a, Vect (minus n (finToNat m)) a)
split {n = n} xs        FZ     = rewrite minusZeroRight n in ([], xs)
split         (x :: xs) (FS m) =
  let (ys, zs) = split xs m in (x :: ys, zs)

-- 18. Extract a slice from a list.
total
slice : Vect n a -> (from, to : Fin n) -> Vect (minus (S (finToNat to)) (finToNat from)) a
slice               (x :: _)  FZ      FZ     = [x]
slice               _         (FS _)  FZ     = []
slice {n = S (S _)} (x :: xs) FZ      (FS t) = x :: slice xs FZ t
slice               (_ :: xs) (FS f)  (FS t) = slice xs f t

-- 19. Rotate a list N places to the left.

-- 20. Remove the K'th element from a list.
total
removeAt : Vect (S n) a -> (i : Fin (S n)) -> Vect n a
removeAt           (_ :: xs) FZ     = xs
removeAt {n = S _} (x :: xs) (FS n) = x :: removeAt xs n

-- 21. Insert an element at a given position into a list.
total
insertAt : Vect n a -> a -> (i : Fin (S n)) -> Vect (S n) a
insertAt xs        y FZ     = y :: xs
insertAt (x :: xs) y (FS i) = x :: insertAt xs y i
