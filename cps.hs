module CPS where

import Control.Monad.State

data Expr
  = Unit
  | Var String
  | LetRec String [String] Expr Expr
  | Abs String Expr
  | App Expr Expr
  | If Expr Expr  -- Non-deterministic branch
  | Fail

instance Show Expr where
  show Unit = "()"
  show (Var x) = x
  show (LetRec f xs e1 e2) = "let " ++ f ++ concatMap (' ' :) xs ++ " = " ++ show e1 ++ " in " ++ show e2
  show (Abs x e) = "fun " ++ x ++ " -> " ++ show e
  show (App e1 e2@(App _ _)) = show e1 ++ " (" ++ show e2 ++ ")"
  show (App e1 e2@(Abs _ _)) = show e1 ++ " (" ++ show e2 ++ ")"
  show (App e1 e2@(If _ _)) = show e1 ++ " (" ++ show e2 ++ ")"
  show (App e1 e2) = show e1 ++ " " ++ show e2
  show (If e1 e2) = "if * then " ++ show e1 ++ " else " ++ show e2
  show Fail = "fail"

loop :: Expr
loop =
  let m  = App (Var "f") (App (Var "loop") Unit)
      e1 = LetRec "f" ["x"] Fail m
      e2 = LetRec "loop" ["x"] (App (Var "loop") (Var "x")) e1
   in e2

fg :: Expr
fg =
  let m = App (Var "f") Unit
      g = LetRec "g" ["x"] (App (Var "f") (Var "x")) m
      f = LetRec "f" ["x"] (If Unit (App (Var "g") (Var "x"))) g
   in f

genNewVar :: String -> State Int String
genNewVar str = do
  i <- get
  put (i + 1)
  return $ str ++ show i

cps :: Expr -> State Int Expr
cps e = case e of
  LetRec f xs e1 e2 ->
    LetRec f xs <$> cps e1 <*> cps e2
  Abs x e -> do
    k <- genNewVar "k"
    e' <- cps e
    return $ Abs k $ App (Var k) (Abs x e')
  App e1 e2 -> do
    k <- genNewVar "k"
    f <- genNewVar "f"
    x <- genNewVar "x"
    e1' <- cps e1
    e2' <- cps e2
    return $ Abs k (App e1' $ Abs f (App e2' $
               Abs x (App (App (Var f) (Var x)) (Var k))))
  If e1 e2 -> do
    k <- genNewVar "k"
    e1' <- cps e1
    e2' <- cps e2
    return $ Abs k $ If (App e1' (Var k)) (App e2' (Var k))
  _ -> do
    k <- genNewVar "k"
    return $ Abs k $ App (Var k) e

subst :: String -> Expr -> Expr -> Expr
subst x t e = case e of
  Unit -> e
  Var y
    | x == y -> t
    | otherwise -> e
  LetRec f xs e1 e2 ->
    LetRec f xs (subst x t e1) (subst x t e2)
  Abs y e
    | x == y -> e
    | otherwise -> Abs y (subst x t e)
  App e1 e2 ->
    App (subst x t e1) (subst x t e2)
  If e1 e2 ->
    If (subst x t e1) (subst x t e2)
  Fail -> e

beta :: Expr -> Expr
beta e = case e of
  LetRec f xs e1 e2 ->
    LetRec f xs (beta e1) (beta e2)
  Abs x e ->
    Abs x (beta e)
  App (Abs x e1) e2 ->
    beta (subst x e2 e1)
  App e1 e2 ->
    App (beta e1) (beta e2)
  If e1 e2 ->
    If (beta e1) (beta e2)
  _ -> e

main :: IO ()
main = do
   print loop
   print $ beta $ evalState (cps loop) 0
   print fg
   print $ beta $ evalState (cps fg) 0
