{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang
import Common
import Text.Parsec hiding (runP,parse)
import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)
import Elab (desugarSdecl)
import Data.Maybe (isJust)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser $
        emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "let rec", "fun", "fix", "then", "else","in",
                           "ifz", "print","Nat", "type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP
         <|> SSynType <$> var

typeP :: P STy
typeP = try (do
          x <- tyatom
          reservedOp "->"
          ---y <- typeP
          SFunTy x <$> typeP)
      <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SPrint i str)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

multibinders :: P [(Name, STy)]
multibinders = do vs <- many var
                  reservedOp ":"
                  ty <- typeP
                  return (map (\x -> (x, ty)) vs)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         try(
           do (v,ty) <- parens binding
              reservedOp "->"
              SLam i [(v, ty)] <$> expr)
           <|> (do lamsugarbody i)

lamsugarbody :: Pos -> P STerm
lamsugarbody i = do (v,ty) <- parens binding
                    binders <- many (parens binding)
                    reservedOp "->"
                    SLam i ((v, ty):binders) <$> expr

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         SIfZ i c t <$> expr

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         (x, xty) <- parens binding
         binders <- many (parens binding)
         reservedOp "->"
         SFix i ((f, fty):((x, xty): binders)) <$> expr

isrec :: P Bool
isrec = try(do reserved "rec"; return True ) <|> return False

letexp :: P STerm
letexp =  do
  i <- getPos
  reserved "let"
  b <- isrec
  bodylet b i

--- parsers para el resto del termino let
--- un resultado con binders vacio seria equivalente a un let sin azucar
bodylet :: Bool -> Pos -> P STerm
bodylet b info = try(do
  (v,ty) <- parens binding <|> binding
  reservedOp "="
  def <- expr
  reserved "in"
  SLet b info v ty [] def <$> expr) <|> sugarbodylet b info

sugarbodylet :: Bool -> Pos -> P STerm
sugarbodylet b info = do
  f <- var
  binders <- many (parens binding)
  reservedOp ":"
  ty <- tyatom
  reservedOp "="
  def <- expr
  reserved "in"
  SLet b info f ty binders def <$> expr

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parser de declaraciones

decl :: P (SDecl STerm)
decl = declSTerm <|> typedecl

declSTerm :: P (SDecl STerm)
declSTerm = do
     i <- getPos
     reserved "let"
     b <- isrec
     v <- var
     binders <- many (parens multibinders)
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     SDecl i b v ty (concat binders) <$> expr

typedecl :: P (SDecl a)
typedecl = do i <- getPos
              reserved "type"
              name <- var
              reserved "="
              SDeclType i name <$> typeP

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
