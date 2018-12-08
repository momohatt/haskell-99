-- 31. Determine whether a given integer number is prime.
isPrime :: Integral a => a -> Bool
isPrime 1 = False
isPrime n = all (\x -> n `mod` x /= 0) [2..(round . sqrt . fromIntegral) n]

-- 32. Determine the greatest common divisor of two positive integer numbers. Use Euclid's algorithm.
myGCD :: Integral a => a -> a -> a
myGCD a b
  | m == n = m
  | m < n  = myGCD (n - m) m
  | m > n  = myGCD (m - n) n
  where m = abs a
        n = abs b

-- 33. Determine whether two positive integer numbers are coprime. Two numbers are coprime if their greatest common divisor equals 1.
coprime :: Integral a => a -> a -> Bool
coprime a b = myGCD a b == 1

-- 34. Calculate Euler's totient function phi(m).
totient :: Integral a => a -> Int
totient 1 = 1
totient n =
    length (filter coprime [1..n])

-- 35. Determine the prime factors of a given positive integer. Construct a flat list containing the prime factors in ascending order.
primeFactors :: Integral a => a -> [a]
primeFactors n = primeFactorHelper n 2
    where primeFactorHelper n d
            | n == 1          = []
            | not (isPrime d) = primeFactorHelper n (d + 1)
            | n `mod` d == 0  = d : primeFactorHelper (n `div` d) d
            | otherwise       = primeFactorHelper n (d + 1)

-- 36. Determine the prime factors of a given positive integer. Construct a list containing the prime factors and their multiplicity.
primeFactorsMult :: Integral a => a -> [(a, a)]
primeFactorsMult n =
    pack (primeFactors n)
        where pack [] = []
              pack (x:xs) =
                  let xs' = pack xs in
                      case xs' of
                        [] -> [(x, 1)]
                        (y, n):ys | x == y -> (y, n + 1):ys
                        (y, n):ys | x /= y -> (x, 1):xs'

-- 37. Calculate Euler's totient function phi(m) (improved).
totientMult :: Integral a => a -> a
totientMult n =
    foldl (\acc (p, m) -> acc * (p - 1) * p ^ (m - 1)) 1 (primeFactorsMult n)

-- 38. Compare the two methods of calculating Euler's totient function.
-- *Main> totient 10090
-- 4032
-- *Main> totientMult 10090
-- 4032

-- 39. Given a range of integers by its lower and upper limit, construct a list of all prime numbers in that range.
primesR :: Integral a => a -> a -> [a]
primesR a b =
    filter isPrime [a..b]

-- 40. Goldbach's conjecture.
goldbach :: Integral a => a -> (a, a)
goldbach n
  | n <= 2    = error "argument must be greater than 2"
  | otherwise = helper n [2..(n `div` 2)]
  where helper n []   = error "No such number"
        helper n (x:xs)
          | isPrime x && isPrime (n - x) = (x, n - x)
          | otherwise = helper n xs

-- 41. Given a range of integers by its lower and upper limit, print a list of all even numbers and their Goldbach composition.
goldbachList :: Integral a => a -> a -> [(a, a)]
goldbachList a b =
    map goldbach (dropWhile (<4) (filter even [a..b]))

goldbachList' :: Integral a => a -> a -> a -> [(a, a)]
goldbachList' a b c =
    filter (\(x, y) -> x >= c && y >= c) (goldbachList a b)
