module Formula where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List (intersperse)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Literal

newtype Clause = Clause { clauseSet :: IntSet }
  deriving (Eq, Ord, Monoid)

newtype Formula = Formula { formulaSet :: Set Clause }
  deriving (Eq, Ord, Monoid)

instance Show Formula where
  showsPrec p = showParen (p > 2) . foldr (.) id
              . List.intersperse (showString " & ") . fmap (showsPrec 3)
              . Set.toList . formulaSet

instance Show Clause where
  showsPrec p = showParen (p > 1) . foldr (.) id
              . List.intersperse (showString " | ") . fmap (showsPrec 2 . Lit)
              . IntSet.toList . clauseSet

clauseLits :: Clause -> [Lit]
clauseLits cl = [ Lit lit | lit <- IntSet.toList (clauseSet cl) ]

formulaEmpty :: Formula
formulaEmpty = Formula Set.empty

formulaLiteral :: Lit -> Formula
formulaLiteral (Lit l) =
  Formula (Set.singleton (Clause (IntSet.singleton l)))

formulaNot :: Lit  -- ^ Output
           -> Lit  -- ^ Input
           -> Formula
formulaNot out inp = formulaFromList cls
  where
    cls = [ [litNeg out, litNeg inp], [out, inp] ]

formulaAnd :: Lit    -- ^ Output
           -> [Lit]  -- ^ Inputs
           -> Formula
formulaAnd out inps = formulaFromList cls
  where
    cls = (out : map litNeg inps) : map (\inp -> [litNeg out, inp]) inps

formulaOr :: Lit    -- ^ Output
          -> [Lit]  -- ^ Inputs
          -> Formula
formulaOr out inps = formulaFromList cls
  where
    cls = (litNeg out : inps)
        : map (\inp -> [out, litNeg inp]) inps

formulaXor :: Lit  -- ^ Output
           -> Lit  -- ^ Input
           -> Lit  -- ^ Input
           -> Formula
formulaXor out inpA inpB = formulaFromList cls
  where
    cls = [ [litNeg out, litNeg inpA, litNeg inpB]
          , [litNeg out, inpA,  inpB]
          , [out, litNeg inpA,  inpB]
          , [out,  inpA, litNeg inpB]
          ]

formulaMux :: Lit  -- ^ Output
           -> Lit  -- ^ False branch
           -> Lit  -- ^ True branch
           -> Lit  -- ^ Predicate/selector
           -> Formula
formulaMux out inpF inpT inpP =
  formulaFromList cls
  where
    cls = [ [litNeg out,  inpF,  inpT]
          , [litNeg out,  inpF,  inpP]
          , [litNeg out,  inpT,  litNeg inpP]
          , [ out, litNeg inpF,  inpP]
          , [ out, litNeg inpT,  litNeg inpP]
          ]

formulaFromList :: [[Lit]] -> Formula
formulaFromList = Formula . Set.fromList . fmap (Clause . IntSet.fromList . fmap litId)

data PropL var
  = Const Bool
  | Atom var
  | Not (PropL var)
  | And (PropL var) (PropL var)
  | Or (PropL var) (PropL var)
  deriving (Eq,Functor,Show)

simplify :: Eq var => PropL var -> PropL var
simplify (Not f) = case simplify f of
  Not f' -> f'
  Const x -> Const $ not x
  And x y -> Or (simplify (Not x)) (simplify (Not y))
  Or x y -> And (simplify (Not x)) (simplify (Not y))
  f' -> Not f'
simplify (And x y) = case (simplify x,simplify y) of
  (Const True,y') -> y'
  (Const False,_) -> Const False
  (x',Const True) -> x'
  (_,Const False) -> Const False
  (x',y') -> if x'==y'
             then x'
             else And x' y'
simplify (Or x y) = case (simplify x,simplify y) of
  (Const True,_) -> Const True
  (Const False,y') -> y'
  (_,Const True) -> Const True
  (x',Const False) -> x'
  (x',y') -> if x'==y'
             then x'
             else Or x' y'
simplify x = x

toCNF :: Monad m => m Var -> PropL Var -> m Formula
toCNF nxt (Const True) = return $ Formula Set.empty
toCNF nxt (Const False) = return $ Formula $ Set.singleton (Clause IntSet.empty)
toCNF nxt (Atom v) = return $ formulaLiteral $ lp v
toCNF nxt (And x y) = do
  fx <- toCNF nxt x
  fy <- toCNF nxt y
  return $ Formula $ Set.union (formulaSet fx) (formulaSet fy)
toCNF nxt (Or x y) = do
  (Clause clx,Formula fx) <- toClause nxt x
  (Clause cly,Formula fy) <- toClause nxt y
  return $ Formula $ Set.insert (Clause $ IntSet.union clx cly) (Set.union fx fy)
toCNF nxt (Not (Const x)) = toCNF nxt (Const $ not x)
toCNF nxt (Not (Not x)) = toCNF nxt x
toCNF nxt (Not (Atom v)) = return $ formulaLiteral $ ln v
toCNF nxt (Not (Or x y)) = toCNF nxt (And (Not x) (Not y))
toCNF nxt (Not (And x y)) = toCNF nxt (Or (Not x) (Not y))

toClause :: Monad m => m Var -> PropL Var -> m (Clause,Formula)
toClause nxt (Const False) = return (Clause IntSet.empty,formulaEmpty)
toClause nxt (Atom v) = return (Clause $ IntSet.singleton $ litId $ lp v,formulaEmpty)
toClause nxt (Or x y) = do
  (Clause clx,Formula fx) <- toClause nxt x
  (Clause cly,Formula fy) <- toClause nxt y
  return (Clause $ IntSet.union clx cly,Formula $ Set.union fx fy)
toClause nxt (Not (Atom v)) = return (Clause $ IntSet.singleton $ litId $ ln v,formulaEmpty)
toClause nxt (Not (And x y)) = toClause nxt (Or (Not x) (Not y))
toClause nxt f = do
  (f',lit) <- tseitin nxt f
  return (Clause $ IntSet.singleton $ litId lit,f')

tseitin :: Monad m => m Var -> PropL Var -> m (Formula,Lit)
tseitin nxt (Atom x) = return (formulaEmpty,lp x)
tseitin nxt (Not (And (Not x) (Not y))) = tseitin nxt (Or x y)
tseitin nxt (Not x) = do
  (f1,lit) <- tseitin nxt x
  return (f1,litNeg lit)
tseitin nxt (And x y) = do
  (Formula cnf_x,l1) <- tseitin nxt x
  (Formula cnf_y,l2) <- tseitin nxt y
  vout <- nxt
  let Formula cnf_r = formulaAnd (lp vout) [l1,l2]
  return (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],lp vout)
tseitin nxt (Or x y) = do
  (Formula cnf_x,l1) <- tseitin nxt x
  (Formula cnf_y,l2) <- tseitin nxt y
  vout <- nxt
  let Formula cnf_r = formulaOr (lp vout) [l1,l2]
  return (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],lp vout)