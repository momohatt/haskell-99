import Data.List

-- 46.
not' :: Bool -> Bool
not' True = False
not' False = True

and' :: Bool -> Bool -> Bool
and' = (&&)

or' :: Bool -> Bool -> Bool
or' = (||)

nand' :: Bool -> Bool -> Bool
nand' b1 b2 = not' (and' b1 b2)

nor' :: Bool -> Bool -> Bool
nor' b1 b2 = not' (or' b1 b2)

xor' :: Bool -> Bool -> Bool
xor' b1 b2 = and' (nand' b1 b2) (or' b1 b2)

impl' :: Bool -> Bool -> Bool
impl' b1 b2 = or' (not' b1) b2

equ' :: Bool -> Bool -> Bool
equ' = (==)

table :: (Bool -> Bool -> Bool) -> IO ()
table f =
    putStrLn $ unlines
    [show a ++ " " ++ show b ++ " " ++ show (f a b) | a <- [True, False], b <- [True, False]]

-- 47.
-- http://walk.northcol.org/haskell/operators/
infixl 4 `or'`
infixl 6 `and'`
infixl 7 `equ'`

-- 48.
tablen :: Int -> ([Bool] -> Bool) -> IO ()
tablen n f =
    putStrLn $ unlines $ map (\b -> concatMap ((++" ") . show) b ++ show (f b)) (powBool n)
        where powBool 0 = []
              powBool 1 = [[True], [False]]
              powBool n = map (True:) (powBool (n - 1)) ++ map (False:) (powBool (n - 1))

-- 49.
gray :: Integral a => a -> [String]
gray 1 = ["0", "1"]
gray n
  | n <= 0    = error "invalid argument"
  | otherwise = map ("0"++) (gray $ n - 1) ++ map ("1"++) (reverse $ gray $ n - 1)

-- 50.
huffman :: (Eq a, Integral b) => [(a, b)] -> [(a, String)]
huffman l =
    let l' = zip [1..(length l)] (map snd l) in
        zip (map fst l) $ map (\(_, _, z) -> z) $ sortBy (\(x, _, _) (y, _, _) -> compare x y) $ helper l'
helper [] = []
helper [(id, p)] = [(id, p, "0")]
helper [a, b] =
    if snd a < snd b then [(fst a, snd a, "0"), (fst b, snd b, "1")]
                     else [(fst b, snd b, "0"), (fst a, snd a, "1")]
helper l =
    let new_id = maximum (map fst l) + 1
        ((x1, y1):(x2, y2):xs) = sortBy (\(_, x) (_, y) -> compare x y) l
        l' = helper ((new_id, y1 + y2) : xs)
     in
        case find (\(id, _, _) -> id == new_id) l' of
          Just (_, _, str) ->
              (x1, y1, str ++ "0") : (x2, y2, str ++ "1") : filter (\(id, _, _) -> id /= new_id) l'
          Nothing -> error "unreached"
