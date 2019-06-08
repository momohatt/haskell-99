-- Monty-Hall problem in Haskell

import System.Random
import Control.Monad

monty :: Int -> Int -> IO Int
monty car choice
  | car == choice = do
    rnd <- randomRIO(0, 1) :: IO Int
    let ghoat = [x | x <- [0..2], x /= choice]
    return (ghoat !! rnd)
  | car /= choice =
    return $ head [x | x <- [0..2], x /= car, x /= choice]

trial :: IO Bool
trial = do
  car <- randomRIO(0, 2) :: IO Int
  choice <- randomRIO(0, 2) :: IO Int
  let open = monty car choice
  return (car == choice)

main :: IO ()
main = do
  let n = 100
  result <- forM [1..n] $ const trial
  let success = length $ filter id result
  putStrLn $ "#trial                               : " ++ show n
  putStrLn $ "#success without changing the choice : " ++ show success
