module DeBrujinIndex where

import           Text.ParserCombinators.Parsec
import           Text.ParserCombinators.Parsec.Language (haskellDef)
import qualified Text.ParserCombinators.Parsec.Token    as P

data Term
  = TVar String
  | TApp Term Term
  | TLambda String Term
  deriving (Show)

data DBTerm
  = DVar Integer
  | DApp DBTerm DBTerm
  | DLambda DBTerm

instance Show DBTerm where
  show (DVar n) = show n
  show (DApp t1 t2@(DVar _)) = show t1 ++ " " ++ show t2
  show (DApp t1 t2) = show t1 ++ " (" ++ show t2 ++ ")"
  show (DLambda t) = "\\ " ++ show t

--
-- Parser
--

lexer :: P.TokenParser ()
lexer = P.makeTokenParser haskellDef

parens = P.parens lexer

parseTerm :: String -> Term
parseTerm input =
  case parse pTerm "" input of
    Left _ -> error "parser"
    Right t -> t

pTerm :: Parser Term
pTerm = try (TLambda <$> (char '\\' >> spaces >> many1 letter)
                    <*> (spaces >> char '.' >> spaces >> pTerm))
    <|> try (TApp <$> pAtom <*> (spaces >> pAtom))
    <|> pAtom

pAtom :: Parser Term
pAtom = try (TVar <$> many1 letter)
    <|> parens pTerm


--
-- Conversion
--

convert' :: Term -> [(String, Integer)] -> Integer -> DBTerm
convert' (TVar x) env n =
  case lookup x env of
    Just m -> DVar (n - m)
    Nothing -> error $ "Unknown variable: " ++ x
convert' (TApp t1 t2) env n =
  DApp (convert' t1 env n) (convert' t2 env n)
convert' (TLambda x t) env n =
  DLambda (convert' t ((x, n) : env) (n + 1))

convert :: String -> DBTerm
convert input =
  convert' (parseTerm input) [] 0

-- Some examples.
-- >>> convert "\\z. (\\y. y (\\x. x)) (\\x. z x)"
-- \ \ 1 (\ 1) (\ 2 1)
-- >>> convert "\\x. \\y. x"
-- \ \ 2
-- >>> convert "\\x. \\y. \\z. (x z) (y z)"
-- \ \ \ 3 1 (2 1)
--
-- Following doesn't work because of the poor parser.
-- >>> convert "\\x. \\y. \\z. x z (y z)"
