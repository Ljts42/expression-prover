module Main where

import Grammar
import Lexer (alexScanTokens)
import Parser

import Data.List (sort, nub, intercalate)
import Data.Map as Map
import Data.Map (insert)
import Data.Maybe
import Data.Set as Set

proveAx1 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx1 l c a b = do -- a->b->a
    (ax (l+2) (a:b:c) a)
    (iImpl (l+1) (a:c) b a)
    (iImpl l c a (Binary Impl b a))

proveAx2 :: Int -> [Expr] -> Expr -> Expr -> Expr -> IO()
proveAx2 l c a b d = do -- (a->b)->(a->b->d)->(a->d)
    (ax (l+5) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) (Binary Impl a (Binary Impl b d)))
    (ax (l+5) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) a)
    (eImpl (l+4) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) a (Binary Impl b d))
    (ax (l+5) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) (Binary Impl a b))
    (ax (l+5) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) a)
    (eImpl (l+4) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) a b)
    (eImpl (l+3) (a:(Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) b d)
    (iImpl (l+2) ((Binary Impl a b):(Binary Impl a (Binary Impl b d)):c) a d)
    (iImpl (l+1) ((Binary Impl a b):c) (Binary Impl a (Binary Impl b d)) (Binary Impl a d))
    (iImpl l c (Binary Impl a b) (Binary Impl (Binary Impl a (Binary Impl b d)) (Binary Impl a d)))

proveAx3 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx3 l c a b = do -- a->b->a&b
    (ax (l+3) (a:b:c) a)
    (ax (l+3) (a:b:c) b)
    (iAnd (l+2) (a:b:c) a b)
    (iImpl (l+1) (a:c) b (Binary And a b))
    (iImpl l c a (Binary Impl b (Binary And a b)))

proveAx4 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx4 l c a b = do -- a&b->a
    (ax (l+2) ((Binary And a b):c) (Binary And a b))
    (elAnd (l+1) ((Binary And a b):c) a b)
    (iImpl l c (Binary And a b) a)

proveAx5 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx5 l c a b = do -- a&b->b
    (ax (l+2) ((Binary And a b):c) (Binary And a b))
    (erAnd (l+1) ((Binary And a b):c) a b)
    (iImpl l c (Binary And a b) b)

proveAx6 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx6 l c a b = do -- a->a|b
    (ax (l+2) (a:c) a)
    (ilOr (l+1) (a:c) a b)
    (iImpl l c a (Binary Or a b))

proveAx7 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx7 l c a b = do -- b->a|b
    (ax (l+2) (b:c) b)
    (irOr (l+1) (b:c) a b)
    (iImpl l c b (Binary Or a b))

proveAx8 :: Int -> [Expr] -> Expr -> Expr -> Expr -> IO()
proveAx8 l c a b d = do -- (a->d)->(b->d)->(a|b->d)
    (ax (l+5) (a:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) (Binary Impl a d))
    (ax (l+5) (a:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) a)
    (eImpl (l+4) (a:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) a d)
    (ax (l+5) (b:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) (Binary Impl b d))
    (ax (l+5) (b:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) b)
    (eImpl (l+4) (b:(Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) b d)
    (ax (l+4) ((Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) (Binary Or a b))
    (eOr (l+3) ((Binary Or a b):(Binary Impl b d):(Binary Impl a d):c) a b d)
    (iImpl (l+2) ((Binary Impl b d):(Binary Impl a d):c) (Binary Or a b) d)
    (iImpl (l+1) ((Binary Impl a d):c) (Binary Impl b d) (Binary Impl (Binary Or a b) d))
    (iImpl l c (Binary Impl a d) (Binary Impl (Binary Impl b d) (Binary Impl (Binary Or a b) d)))

proveAx9 :: Int -> [Expr] -> Expr -> Expr -> IO()
proveAx9 l c a b = proveAx2 l c a b Not -- (a->b)->(a->b->!)->(a->!)

proveAx10 :: Int -> [Expr] -> Expr -> IO()
proveAx10 l c a = do -- ((a->!)->!)->a
    (ax (l+3) ((Binary Impl a Not):(Binary Impl (Binary Impl a Not) Not):c) (Binary Impl (Binary Impl a Not) Not))
    (ax (l+3) ((Binary Impl a Not):(Binary Impl (Binary Impl a Not) Not):c) (Binary Impl a Not))
    (eImpl (l+2) ((Binary Impl a Not):(Binary Impl (Binary Impl a Not) Not):c) (Binary Impl a Not) Not)
    (eNN (l+1) ((Binary Impl (Binary Impl a Not) Not):c) a)
    (iImpl l c (Binary Impl (Binary Impl a Not) Not) a)

proveAnotA :: Int -> [Expr] -> Expr -> IO()
proveAnotA l c a = do
    (ax    (l+9) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)))
    (ax    (l+9) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not))
    (eImpl (l+8) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl (Binary Impl a Not) Not))
    (ax    (l+9) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)))
    (ax    (l+9) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not))
    (eImpl (l+8) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl a Not))
    (eImpl (l+7) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a Not)
    (iImpl (l+6) ((Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not) Not)
    (iImpl (l+5) ((Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) Not))
    (iImpl (l+4) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not)) (Binary Impl (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) Not)))
    (ax    (l+7) (a:(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not))
    (ax    (l+8) (a:(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a)
    (ilOr  (l+7) (a:(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl a Not))
    (eImpl (l+6) (a:(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a Not)
    (iImpl (l+5) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a Not)
    (iImpl (l+4) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl a Not))
    (eImpl (l+3) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not)) (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) Not)))
    (ax    (l+6) ((Binary Impl a Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not))
    (ax    (l+7) ((Binary Impl a Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl a Not))
    (irOr  (l+6) ((Binary Impl a Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl a Not))
    (eImpl (l+5) ((Binary Impl a Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a Not)
    (iImpl (l+4) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):(Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl a Not) Not)
    (iImpl (l+3) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not) (Binary Impl (Binary Impl a Not) Not))
    (eImpl (l+2) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a (Binary Impl (Binary Impl (Binary Or a (Binary Impl a Not)) Not) Not))
    (ax    (l+2) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) (Binary Impl (Binary Or a (Binary Impl a Not)) Not))
    (eImpl (l+1) ((Binary Impl (Binary Or a (Binary Impl a Not)) Not):c) a Not)
    (eNN   l     c (Binary Or a (Binary Impl a Not)))

-- D
getVariables :: Expr -> Set Expr
getVariables (Binary op a b) = Set.union (getVariables a) (getVariables b)
getVariables Not = Set.empty
getVariables v = Set.singleton v

eval :: Expr -> (Set Expr) -> Bool
eval Not _ = False
eval e@(Var _) values = Set.member e values
eval (Binary Impl e@(Var _) Not) values = not (Set.member e values)
eval (Binary op a b) values = case op of
  Impl -> not (eval a values) || eval b values
  Or   -> eval a values || eval b values
  And  -> eval a values && eval b values

check :: [Expr] -> Expr -> (Set Expr) -> [Expr]
check [] e v = if not (eval e v) then Set.toList v else []
check [x] e v = case (check [] e (Set.insert x v)) of
    [] -> check [] e (Set.insert (Binary Impl x Not) v)
    r -> r
check (x:xs) e v = case (check xs e (Set.insert x v)) of
    [] -> check xs e (Set.insert (Binary Impl x Not) v)
    r -> r

hypothesis :: Int -> [Expr] -> Expr -> (Set Expr) -> [Expr] -> IO()
hypothesis l c (Binary Impl a (Binary Impl b a2)) _ _ | a == a2    = proveAx1 l c a b
hypothesis l c (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Binary Impl b2 d)) (Binary Impl a3 d2))) _ _
      | a == a2 && a2 == a3 && b == b2 && d == d2  = proveAx2 l c a b d
hypothesis l c (Binary Impl a (Binary Impl b (Binary And a2 b2))) _ _
      | a == a2 && b == b2                         = proveAx3 l c a b
hypothesis l c (Binary Impl (Binary And a b) a2) _ _
      | a == a2                                    = proveAx4 l c a b
hypothesis l c (Binary Impl (Binary And a b) b2) _ _
      | b == b2                                    = proveAx5 l c a b
hypothesis l c (Binary Impl a (Binary Or a2 b)) _ _
      | a == a2                                    = proveAx6 l c a b
hypothesis l c (Binary Impl b (Binary Or a b2)) _ _
      | b == b2                                    = proveAx7 l c a b
hypothesis l c (Binary Impl (Binary Impl a d) (Binary Impl (Binary Impl b d2) (Binary Impl (Binary Or a2 b2) d3))) _ _
      | a == a2 && b == b2 && d == d2 && d2 == d3  = proveAx8 l c a b d
hypothesis l c (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Binary Impl b2 Not)) (Binary Impl a3 Not))) _ _
      | a == a2 && a2 == a3 && b == b2             = proveAx9 l c a b
hypothesis l c (Binary Impl (Binary Impl (Binary Impl a Not) Not) a2) _ _
      | a == a2                                    = proveAx10 l c a
hypothesis l c (Binary Or a (Binary Impl a2 Not)) _ _
      | a == a2                                    = proveAnotA l c a
hypothesis l c e v [] = prove l c e v
hypothesis l c b v (a:xs) = do
    (hypothesis (l+1) (a:c) b (Set.insert a v) xs)
    (hypothesis (l+1) ((Binary Impl a Not):c) b (Set.insert (Binary Impl a Not) v) xs)
    (proveAnotA (l+1) c a)
    (eOr l c a (Binary Impl a Not) b)

prove :: Int -> [Expr] -> Expr -> (Set Expr) -> IO()
prove l c (Binary Impl a (Binary Impl b a2)) _ | a == a2    = proveAx1 l c a b
prove l c (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Binary Impl b2 d)) (Binary Impl a3 d2))) _
      | a == a2 && a2 == a3 && b == b2 && d == d2  = proveAx2 l c a b d
prove l c (Binary Impl a (Binary Impl b (Binary And a2 b2))) _
      | a == a2 && b == b2                         = proveAx3 l c a b
prove l c (Binary Impl (Binary And a b) a2) _
      | a == a2                                    = proveAx4 l c a b
prove l c (Binary Impl (Binary And a b) b2) _
      | b == b2                                    = proveAx5 l c a b
prove l c (Binary Impl a (Binary Or a2 b)) _
      | a == a2                                    = proveAx6 l c a b
prove l c (Binary Impl b (Binary Or a b2)) _
      | b == b2                                    = proveAx7 l c a b
prove l c (Binary Impl (Binary Impl a d) (Binary Impl (Binary Impl b d2) (Binary Impl (Binary Or a2 b2) d3))) _
      | a == a2 && b == b2 && d == d2 && d2 == d3  = proveAx8 l c a b d
prove l c (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a2 (Binary Impl b2 Not)) (Binary Impl a3 Not))) _
      | a == a2 && a2 == a3 && b == b2             = proveAx9 l c a b
prove l c (Binary Impl (Binary Impl (Binary Impl a Not) Not) a2) _
      | a == a2                                    = proveAx10 l c a
prove l c (Binary Or a (Binary Impl a2 Not)) _
      | a == a2                                    = proveAnotA l c a
prove l c (Binary Impl Not a) _ = do
    (ax (l+2) (Not:(Binary Impl a Not):c) Not)
    (eNN (l+1) (Not:c) a)
    (iImpl l c Not a)
prove l c x@(Var _) _ = putStrLn (show (Proof l (Line c x) Ax))
prove l c nx@(Binary Impl (Var _) Not) _ = putStrLn (show (Proof l (Line c nx) Ax))
prove l c (Binary Impl (Binary Impl a Not) Not) v = do
    (ax (l+2) ((Binary Impl a Not):c) (Binary Impl a Not))
    (prove (l+2) ((Binary Impl a Not):c) a v)
    (eImpl (l+1) ((Binary Impl a Not):c) a Not)
    (iImpl l c (Binary Impl a Not) Not) -- nnA

prove l c (Binary Impl (Binary And a b) Not) v = if eval a v
    then do
        (prove (l + 2) ((Binary And a b):c) (Binary Impl b Not) v)
        (ax (l+3) ((Binary And a b):c) (Binary And a b))
        (erAnd (l+2) ((Binary And a b):c) a b)
        (eImpl (l+1) ((Binary And a b):c) b Not)
        (iImpl l c (Binary And a b) Not) -- and10
    else if eval b v
        then do
            (prove (l + 2) ((Binary And a b):c) (Binary Impl a Not) v)
            (ax (l+3) ((Binary And a b):c) (Binary And a b))
            (elAnd (l+2) ((Binary And a b):c) a b)
            (eImpl (l+1) ((Binary And a b):c) a Not)
            (iImpl l c (Binary And a b) Not) -- and01
        else do
            (prove (l + 2) ((Binary And a b):c) (Binary Impl a Not) v) -- or b->=_|_
            (ax (l+3) ((Binary And a b):c) (Binary And a b))
            (elAnd (l+2) ((Binary And a b):c) a b) -- or erAnd
            (eImpl (l+1) ((Binary And a b):c) a Not) -- or b->_|_
            (iImpl l c (Binary And a b) Not) -- and00
prove l c (Binary Impl (Binary Or a b) Not) v = do
    (prove (l+3) (a:(Binary Or a b):c) (Binary Impl a Not) v)
    (ax (l+3) (a:(Binary Or a b):c) a)
    (eImpl (l+2) (a:(Binary Or a b):c) a Not)
    (prove (l + 3) (b:(Binary Or a b):c) (Binary Impl b Not) v)
    (ax (l+3) (b:(Binary Or a b):c) b)
    (eImpl (l+2) (b:(Binary Or a b):c) b Not)
    (ax (l+2) ((Binary Or a b):c) (Binary Or a b))
    (eOr (l+1) ((Binary Or a b):c) a b Not)
    (iImpl l c (Binary Or a b) Not) -- or00
prove l c (Binary Impl (Binary Impl a b) Not) v = do
    (prove (l+2) ((Binary Impl a b):c) (Binary Impl b Not) v)
    (ax (l+3) ((Binary Impl a b):c) (Binary Impl a b))
    (prove (l+3) ((Binary Impl a b):c) a v)
    (eImpl (l+2) ((Binary Impl a b):c) a b)
    (eImpl (l+1) ((Binary Impl a b):c) b Not)
    (iImpl l c (Binary Impl a b) Not) -- impl10
prove l c (Binary And a b) v = do
    (prove (l+1) c a v)
    (prove (l+1) c b v)
    (iAnd l c a b) -- and11
prove l c (Binary Or a b) v = if eval a v
    then if eval b v
        then do
            (prove (l+1) c a v) -- or b and irOr
            (ilOr l c a b) -- or11
        else do
            (prove (l+1) c a v)
            (ilOr l c a b) -- or10
    else do
        (prove (l+1) c b v)
        (irOr l c a b) -- or01
prove l c (Binary Impl a b) v = if eval a v
    then do
        (prove (l+1) (a:c) b v)
        (iImpl l c a b) -- impl11
    else if eval b v
        then do
            (prove (l+1) (a:c) b v)
            (iImpl l c a b) -- impl01
        else do
            (prove (l+3) (a:(Binary Impl b Not):c) (Binary Impl a Not) v)
            (ax (l+3) (a:(Binary Impl b Not):c) a)
            (eImpl (l+2) (a:(Binary Impl b Not):c) a Not)
            (eNN (l+1) (a:c) b)
            (iImpl l c a b) -- impl00

ax :: Int -> [Expr] -> Expr -> IO()
ax l c a = putStrLn (show (Proof l (Line c a) Ax))
iImpl :: Int -> [Expr] -> Expr -> Expr -> IO()
iImpl l c a b = putStrLn (show (Proof l (Line c (Binary Impl a b)) InsImpl))
eImpl :: Int -> [Expr] -> Expr -> Expr -> IO()
eImpl l c _ b = putStrLn (show (Proof l (Line c b) ErImpl))
iAnd :: Int -> [Expr] -> Expr -> Expr -> IO()
iAnd l c a b = putStrLn (show (Proof l (Line c (Binary And a b)) InsAnd))
elAnd :: Int -> [Expr] -> Expr -> Expr -> IO()
elAnd l c a _ = putStrLn (show (Proof l (Line c a) ErLAnd))
erAnd :: Int -> [Expr] -> Expr -> Expr -> IO()
erAnd l c _ b = putStrLn (show (Proof l (Line c b) ErRAnd))
ilOr :: Int -> [Expr] -> Expr -> Expr -> IO()
ilOr l c a b = putStrLn (show (Proof l (Line c (Binary Or a b)) InsLOr))
irOr :: Int -> [Expr] -> Expr -> Expr -> IO()
irOr l c a b = putStrLn (show (Proof l (Line c (Binary Or a b)) InsROr))
eOr :: Int -> [Expr] -> Expr -> Expr -> Expr -> IO()
eOr l c _ _ d = putStrLn (show (Proof l (Line c d) ErOr))
eNN :: Int -> [Expr] -> Expr -> IO()
eNN l c a = putStrLn (show (Proof l (Line c a) ErNN))

estimation :: [Expr] -> [String]
estimation []                             = []
estimation ((Var x):xs)                   = (x ++ ":=T"):(estimation xs)
estimation ((Binary Impl (Var x) Not):xs) = (x ++ ":=F"):(estimation xs)

main :: IO ()
main = do
    input <- getLine
    let expr = parseExpr $ alexScanTokens input
    let vars =  Set.toList $ getVariables expr
    let false = check vars expr Set.empty
    if false == [] && (eval expr (Set.fromList false))
        then (hypothesis 0 [] expr Set.empty vars)
        else putStrLn ("Formula is refutable [" ++ (intercalate "," $ estimation false) ++ "]")