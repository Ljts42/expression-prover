module Grammar where

import Data.List (intercalate)

data Binop = Impl | Or | And deriving (Eq, Ord)

instance Show Binop where
  show Impl = "->"
  show Or   = "|"
  show And  = "&"

data Expr = Binary Binop Expr Expr
          -- | Not Expr
          | Var String
          | Not
          deriving (Eq, Ord)

instance Show Expr where
  show (Binary op a b) = "(" ++ show a ++ show op ++ show b ++ ")"
  show (Not)      = "_|_"
  show (Var name)      = name

data Line = Line [Expr] Expr

instance Show Line where
  show (Line c e)  = intercalate "|-" [intercalate "," $ map show c, show e]

data Annotation = Hypothesis Int
            | Axiom Int
            | ModusPonens Int Int
            | Deduction Int
            | Incorrect

instance Show Annotation where
  show (Hypothesis i)     = " [Hyp. " ++ show i ++ "]"
  show (Axiom i)          = " [Ax. sch. " ++ show i ++ "]"
  show (ModusPonens i j)  = " [M.P. " ++ show i ++ ", " ++ show j ++ "]"
  show (Deduction i)      = " [Ded. " ++ show i ++ "]"
  show (Incorrect)        = " [Incorrect]"

data Rule = Ax | ErImpl | InsImpl | InsAnd | ErLAnd
         | ErRAnd | InsLOr | InsROr | ErOr | ErNN

instance Show Rule where
  show Ax      = " [Ax]"
  show ErImpl  = " [E->]"
  show InsImpl = " [I->]"
  show InsAnd  = " [I&]"
  show ErLAnd  = " [El&]"
  show ErRAnd  = " [Er&]"
  show InsLOr  = " [Il|]"
  show InsROr  = " [Ir|]"
  show ErOr    = " [E|]"
  show ErNN    = " [E!!]"

data Proof = Proof Int Line Rule

instance Show Proof where
  show (Proof l e r) = "[" ++ show l ++ "] " ++ show e ++ show r