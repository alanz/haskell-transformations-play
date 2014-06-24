{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- import Generics.MultiRec.Base
import Control.Monad
import Generics.MultiRec.Any
import Generics.MultiRec.Rewriting.Machinery
import Generics.MultiRec.TH as M
import System.IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language

import qualified Generics.MultiRec.LR as M
import qualified Generics.MultiRec.Zipper as MZ
import qualified Generics.MultiRec.Rewriting.Rules as M
import qualified Generics.MultiRec.Transformations.Explicit as ME
import qualified Generics.MultiRec.Transformations.RewriteRules as MR
import qualified Generics.MultiRec.Transformations.ZipperState as ZM

import qualified Generics.Regular as R
import qualified Generics.Regular.Base as R
import qualified Generics.Regular.Functions as R
import qualified Generics.Regular.Functions.Read as G
import qualified Generics.Regular.Functions.Show as G
import qualified Generics.Regular.Rewriting.Machinery as R
import qualified Generics.Regular.Rewriting.Rules as R
import qualified Generics.Regular.Transformations.Explicit as E
import qualified Generics.Regular.Transformations.RewriteRules as R
import qualified Generics.Regular.Transformations.RewriteRules as R
import qualified Generics.Regular.Transformations.ZipperState as ZS
import qualified Generics.Regular.Zipper as Z
import qualified Text.ParserCombinators.Parsec.Expr as P
import qualified Text.ParserCombinators.Parsec.Token as Token
{-

Experimentation with 'Generic representations of tree transformations'
by Bransen and Magalhães, 2013
http://dreixel.net/research/pdf/grtt.pdf
-}

-- ---------------------------------------------------------------------

main = putStrLn "hello"

-- ---------------------------------------------------------------------


data Expr = Var String
          | Const Integer
          | Neg Expr
          | Add Expr Expr
          deriving (Show,Ord,Eq)

expr1,expr2,expr3 :: Expr
expr1 = Add (Const 1) (Var "a")
expr2 = Add (Const 1) (Neg (Var "a"))
expr3 = Add (Var "a") (Const 1)

-- Section 3.1

type ExprPF = R.K String  -- Var String
          R.:+: R.K Integer -- Const Integer
          R.:+: R.I         -- Neg Expr
          R.:+: (R.I R.:*: R.I) -- Add Expr Expr

-- type level fixpoint operator
-- data Mu phi =In (phi (Mu phi))

-- so Mu ExprPF encodes a datatype that is isomorphic to Expr

-- 3.2 Functoriality of the representation types

type instance R.PF Expr = ExprPF

instance R.Regular Expr where
  from (Var s)     = R.L (R.K s)
  from (Const i)   = R.R (R.L (R.K i))
  from (Neg e)     = R.R (R.R (R.L (R.I e)))
  from (Add e1 e2) = R.R (R.R (R.R (R.I e1 R.:*: R.I e2)))

  to (R.L (R.K s))                           = Var s
  to (R.R (R.L (R.K i)))                     = Const i
  to (R.R (R.R (R.L (R.I e))))               = Neg e
  to (R.R (R.R (R.R (R.I e1 R.:*: R.I e2)))) = Add e1 e2

-- 3.4 Generic functions -----------------------------------------------

class Children phi where
   gchildren:: phi r -> [r]

instance Children R.U where
  gchildren _ = []

instance Children R.I where
  gchildren (R.I x) = [x]

instance Children (R.K α) where
  gchildren _ = []

instance (Children φ,Children ψ) => Children (φ R.:+: ψ) where
  gchildren (R.L x)= gchildren x
  gchildren (R.R x)= gchildren x

instance (Children φ,Children ψ) => Children (φ R.:*: ψ) where
  gchildren (x R.:*: y) = gchildren x ++ gchildren y

children:: (R.Regular α,Children (R.PF α)) => α -> [α]
children = gchildren . R.from

{-
*Main> children expr1
[Const 1,Var "a"]
*Main> children expr2
[Const 1,Neg (Var "a")]
*Main> children expr3
[Var "a",Const 1]
*Main>
-}

-- 4. Transformation in a zipper with state ----------------------------

insert :: Maybe Expr
insert = ZS.navigate expr1 $ do
   ZS.downMonad
   ZS.rightMonad
   ZS.updateMonad Neg

{-
*Main> expr1
Add (Const 1) (Var "a")
*Main> insert
Just (Add (Const 1) (Neg (Var "a")))
*Main>
-}

delete :: Maybe Expr
delete = ZS.navigate expr2 $ do
  ZS.downMonad
  ZS.rightMonad
  r <- ZS.downMonad
  ZS.upMonad
  ZS.updateMonad (const r)

{-
*Main> expr2
Add (Const 1) (Neg (Var "a"))
*Main> delete
Just (Add (Const 1) (Var "a"))
*Main>
-}

-- 4.1 The Zipper ------------------------------------------------------

-- These next ones are defined in Generics.Regular.Zipper too
{-
data Loc α where
   Loc :: (Regular α,Zipper (PF α))
        => α -> [Ctx (PF α) α ] -> Loc α

data family Ctx (φ :: * -> *) :: * -> *

class Functor φ => Zipper φ where
  cmap        :: (α -> β) -> Ctx φ α -> Ctx φ β
  fill        :: Ctx φ α -> α -> φ α
  first, last :: φ α -> Maybe (α,Ctx φ α)
  next, prev  :: Ctx φ α -> α -> Maybe (α,Ctx φ α)

enter :: (Regular α,Zipper (PF α)) => α -> Loc α
leave :: Loc α -> α
up, down, left, right :: Loc α -> Maybe (Loc α)
on ::Loc α →α
updateM :: Monad φ => (α -> φ α) -> Loc α -> φ (Loc α)
-}

-- 4.2 Adding State to a zipper ----------------------------------------

-- example

swap :: Maybe Expr
swap = ZS.navigate expr1 $
  do l <- ZS.downMonad
     r <- ZS.rightMonad
     ZS.updateMonad (const l)
     ZS.leftMonad
     ZS.updateMonad (const r)

{-
*Main> expr1
Add (Const 1) (Var "a")
*Main> swap
Just (Add (Var "a") (Const 1))
*Main>
-}

-- =====================================================================
-- 5. Transformation by rewriting --------------------------------------

-- 5.1 Generic rewriting

type Ext φ = R.K R.Metavar R.:+: φ
-- type Scheme φ = Mu (Ext φ)
-- type Metavar = Int
-- type SchemeOf α = Scheme (PF α)

-- infix 5 :~>
-- data RuleSpec α = α :~> α
-- type Rule α = RuleSpec (SchemeOf α)

swapExpr :: R.Rule Expr
swapExpr = R.rule $ \ a b -> Add a b R.:~> Add b a

-- rewriteM :: (Rewrite α,Monad φ) => Rule α -> α  -> φ α

-- 5.2 Transformations by rewriting ------------------------------------

{-
apply :: (Regular α,Rewrite α,Z.Zipper (PF α),Transform α)
   => Transformation α -> α -> Maybe α
apply rs = fmap Z.leave . flip (foldM appRule) rs . Z.enter
  where
     appRule a (l,r) = l a >>= Z.updateM (rewriteM r)
-}

instance R.Transform Expr where

delete1 ::Maybe Expr
delete1 = R.apply [(Z.down >=> Z.right,removeNeg)] expr2 where
  removeNeg :: R.Rule Expr
  removeNeg = R.rule $ \ x -> Neg x R.:~> x

{-
*Main> delete1
Just (Add (Const 1) (Var "a"))
*Main> expr2
Add (Const 1) (Neg (Var "a"))
*Main>
-}

swap1 :: Maybe Expr
swap1 = R.apply [(return,swapExpr)] expr1

{-
*Main> swap1
Just (Add (Var "a") (Const 1))
*Main> expr1
Add (Const 1) (Var "a")
*Main>
-}

expandedSwap:: R.Rule Expr
expandedSwap =
   R.In (R.R (R.R (R.R (R.R
      (R.I (R.In (R.L (R.K 0))) R.:*: R.I (R.In (R.L (R.K 1))))))))
 R.:~>
   R.In (R.R (R.R (R.R (R.R
       (R.I (R.In (R.L (R.K 1))) R.:*: R.I (R.In (R.L (R.K 0))))))))

-- =====================================================================
-- 6. Explicit encoding of transformations

-- 6.1 Representation

{-
type Path = [Int]

data WithRef α β = InR (PF α β)
                 | Ref Path
-}

-- type Transformation α =[(Path, Fix (WithRef α))]

instance E.Transform Expr where

insert1 :: Maybe Expr
insert1 = E.apply addNeg expr1 where
   addNeg :: E.Transformation Expr
   addNeg = [([1] , R.In . E.InR . R.R . R.R . R.L . R.I  . R.In $ E.Ref [1])]

{-
*Main> insert1
Just (Add (Const 1) (Neg (Var "a")))
*Main> expr1
Add (Const 1) (Var "a")
*Main>
-}

data ExprEH  = VarEH String
             | ConstEH Integer
             | NegEH ExprEH
             | AddEH ExprEH ExprEH
             | RefEH E.Path


instance E.HasRef Expr where
  type RefRep Expr = ExprEH

  toRef (E.Ref p)                                       = RefEH p
  toRef (E.InR (R.L (R.K s)))                           = VarEH s
  toRef (E.InR (R.R (R.L (R.K i))))                     = ConstEH i
  toRef (E.InR (R.R (R.R (R.L (R.I e)))))               = NegEH e
  toRef (E.InR (R.R (R.R (R.R (R.I e1 R.:*: R.I e2))))) = AddEH e1 e2

  fromRef (VarEH s)     = (E.InR (R.L (R.K s)))
  fromRef (ConstEH i)   = (E.InR (R.R (R.L (R.K i))))
  fromRef (NegEH e)     = (E.InR (R.R (R.R (R.L (R.I e)))))
  fromRef (AddEH e1 e2) = (E.InR (R.R (R.R (R.R (R.I e1 R.:*: R.I e2)))))
  fromRef (RefEH p)     = (E.Ref p)

type TransformationEH α =[(E.Path,E.RefRep α)]

insert2 :: Maybe Expr
insert2 = E.apply (E.fromNiceTransformation addNeg) expr1 where
   addNeg :: TransformationEH Expr
   addNeg=[([1],NegEH (RefEH [1]))]

{-
*Main> insert2
Just (Add (Const 1) (Neg (Var "a")))
*Main> expr1
Add (Const 1) (Var "a")
*Main>
-}

-- =====================================================================
-- 7 MULTIREC


-- 7.2 Examples

type AExpr = Expr
data BExpr = BConst Bool
           | Not BExpr
           | And BExpr BExpr
           | Greater AExpr AExpr
           deriving (Show,Ord,Eq)

data Stmt = Seq [Stmt]
          | Assign String AExpr
          | If BExpr Stmt Stmt
          | While BExpr Stmt
          | Skip
           deriving (Show,Ord,Eq)

data AST l where
  BExpr :: AST BExpr
  AExpr :: AST AExpr
  Stmt  :: AST Stmt

$(M.deriveAll ''AST)


-- ---------------------------------------------------------------------

-- from http://www.haskell.org/haskellwiki/Parsing_a_simple_imperative_language

parseString :: String -> Stmt
parseString str =
  case parse whileParser "" str of
    Left e  -> error $ show e
    Right r -> r

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedNames   = [ "if"
                                     , "then"
                                     , "else"
                                     , "while"
                                     , "do"
                                     , "skip"
                                     , "true"
                                     , "false"
                                     , "not"
                                     , "and"
                                     , "or"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", ":="
                                     , "<", ">", "and", "or", "not"
                                     ]
           }

-- lexer :: Token.GenTokenParser String u Identity
lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

-- ----------------

whileParser :: Parser Stmt
whileParser = whiteSpace >> statement

statement :: Parser Stmt
statement =   parens statement
          <|> sequenceOfStmt

sequenceOfStmt =
  do list <- (sepBy1 statement' semi)
     -- If there's only one statement return it without using Seq.
     return $ if length list == 1 then head list else Seq list

statement' :: Parser Stmt
statement' =   ifStmt
           <|> whileStmt
           <|> skipStmt
           <|> assignStmt

ifStmt :: Parser Stmt
ifStmt =
  do reserved "if"
     cond  <- bExpression
     reserved "then"
     stmt1 <- statement
     reserved "else"
     stmt2 <- statement
     return $ If cond stmt1 stmt2

whileStmt :: Parser Stmt
whileStmt =
  do reserved "while"
     cond <- bExpression
     reserved "do"
     stmt <- statement
     return $ While cond stmt

assignStmt :: Parser Stmt
assignStmt =
  do var  <- identifier
     reservedOp ":="
     expr <- aExpression
     return $ Assign var expr

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

aExpression :: Parser AExpr
aExpression = P.buildExpressionParser aOperators aTerm

bExpression :: Parser BExpr
bExpression = P.buildExpressionParser bOperators bTerm

aOperators = [ [P.Prefix (reservedOp "-"   >> return (Neg             ))          ]
             -- , [P.Infix  (reservedOp "*"   >> return (ABinary Multiply)) AssocLeft]
             -- , [P.Infix  (reservedOp "/"   >> return (ABinary Divide  )) AssocLeft]
             , [P.Infix  (reservedOp "+"   >> return (Add     )) P.AssocLeft]
             -- , [P.Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
              ]

bOperators = [ [P.Prefix (reservedOp "not" >> return (Not             ))          ]
             , [P.Infix  (reservedOp "and" >> return (And     )) P.AssocLeft]
             -- , [P.Infix  (reservedOp ">"   >> return (Greater    )) P.AssocLeft]
             ]

aTerm =  parens aExpression
     <|> liftM Var identifier
     <|> liftM Const integer

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BConst True ))
     <|> (reserved "false" >> return (BConst False))
     <|> rExpression
     -- <|> relation


rExpression =
  do a1 <- aExpression
     op <- relation
     a2 <- aExpression
     -- return $ RBinary op a1 a2
     return $ op a1 a2

relation =   (reservedOp ">" >> return Greater)
         -- <|> (reservedOp "<" >> return Less)

-- ---------------------------------------------------------------------

prog1 :: Stmt
prog1 = parseString $
    "a := 1;"
 ++ "b := a + 2;"
 ++ "if b > 3"
 ++ "then a := 2"
 ++ "else b := 1"

{-
*Main>
*Main> prog1
Seq [Assign "a" (Const 1),Assign "b" (Add (Var "a") (Const 2)),If (Greater (Var "b") (Const 3)) (Assign "a" (Const 2)) (Assign "b" (Const 1))]
-}

prog1' :: Stmt
prog1' =
  Seq [Assign "a" (Const 1)
      ,Assign "b" (Add (Var "a") (Const 2))
      ,If (Greater (Var "b") (Const 3))
          (Assign "a" (Const 2))
          (Assign "b" (Const 1))
      ]

prog2 :: Stmt
prog2 =parseString $
     "a := 1;"
  ++ "b := a + 2;"
  ++ "if not (b > 3)"
  ++ "then b := 1"
  ++ "else a := 2"

{-
*Main> prog2
Seq [Assign "a" (Const 1),Assign "b" (Add (Var "a") (Const 2)),If (Not (Greater (Var "b") (Const 3))) (Assign "b" (Const 1)) (Assign "a" (Const 2))]
*Main>
-}

prog2' :: Stmt
prog2' =
  Seq [Assign "a" (Const 1)
      ,Assign "b" (Add (Var "a") (Const 2))
      ,If (Not (Greater (Var "b") (Const 3)))
          (Assign "b" (Const 1))
          (Assign "a" (Const 2))
     ]

-- instance M.Transform Stmt where
-- type instance PF Stmt = StmtPF

-- instance Z.Zipper (PF Stmt) where

exampleZS :: Maybe Stmt
exampleZS = ZM.navigate Stmt prog1 $
   do ZM.downMonad
      ZM.rightMonad
      ZM.rightMonad
      -- Swap
      ZM.downMonad
      l <- ZM.rightMonad
      r <- ZM.rightMonad
      ZM.updateMonad (\p _ -> matchAny p l)
      ZM.leftMonad
      ZM.updateMonad (\p _ -> matchAny p r)
      -- Add negation
      ZM.leftMonad

      ZM.updateMonad
          (\ p e -> case p of
            BExpr -> Just (Not e)
            _  -> Nothing)

{-
*Main> exampleZS
Just (Seq [Assign "a" (Const 1),Assign "b" (Add (Var "a") (Const 2)),If (Not (Greater (Var "b") (Const 3))) (Assign "b" (Const 1)) (Assign "a" (Const 2))])
-}
exampleZS' =
  Seq [Assign "a" (Const 1)
      ,Assign "b" (Add (Var "a") (Const 2))
      ,If (Not (Greater (Var "b") (Const 3)))
          (Assign "b" (Const 1))
          (Assign "a" (Const 2))
      ]


-- ---------------------------------------------------------------------

instance ME.OrdI AST where

instance MR.Transform AST where
instance M.LRBase Expr where
  leftb = Var "l"
  rightb = Const 1

exampleRR = MR.apply [MR.insert (MZ.down >=> MZ.right >=> MZ.right) swap
                     ,
                      MR.insert MZ.down addNot] Stmt prog1
   where
     swap :: M.Rule AST Stmt
     swap = M.rule $ \e a b -> If e a b M.:~> If e b a

     addNot :: M.Rule AST BExpr
     addNot = M.rule $ \e -> e M.:~> Not e

{-
*Main> exampleRR
Just (Seq [Assign "a" (Const 1),Assign "b" (Add (Var "a") (Const 2)),If (Not (Greater (Var "b") (Const 3))) (Assign "b" (Const 1)) (Assign "a" (Const 2))])
-}
exampleRR' =
  Seq [Assign "a" (Const 1)
      ,Assign "b" (Add (Var "a") (Const 2))
      ,If (Not (Greater (Var "b") (Const 3)))
          (Assign "b" (Const 1))
          (Assign "a" (Const 2))]
