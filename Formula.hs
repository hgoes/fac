module Formula where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List (intersperse)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Control.Applicative
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
  = Atom var
  | Not (PropL var)
  | And (PropL var) (PropL var)
  | Or (PropL var) (PropL var)
  deriving (Functor)

toCNF :: PropL Var -> Var -> (Formula,Var)
toCNF (Atom v) nxt = (formulaLiteral $ lp v,nxt)
toCNF (And x y) nxt = let (fx,nxt1) = toCNF x nxt
                          (fy,nxt2) = toCNF y nxt1
                      in (Formula $ Set.union (formulaSet fx) (formulaSet fy),nxt2)
toCNF (Or x y) nxt = let (Clause clx,Formula fx,nxt1) = toClause x nxt
                         (Clause cly,Formula fy,nxt2) = toClause y nxt1
                     in (Formula $ Set.insert (Clause $ IntSet.union clx cly) (Set.union fx fy),nxt2)
toCNF (Not (Not x)) nxt = toCNF x nxt
toCNF (Not (Atom v)) nxt = (formulaLiteral $ ln v,nxt)
toCNF (Not (Or x y)) nxt = toCNF (And (Not x) (Not y)) nxt
toCNF (Not (And x y)) nxt = toCNF (Or (Not x) (Not y)) nxt

toClause :: PropL Var -> Var -> (Clause,Formula,Var)
toClause (Atom v) nxt = (Clause $ IntSet.singleton $ litId $ lp v,formulaEmpty,nxt)
toClause (Or x y) nxt = let (Clause clx,Formula fx,nxt1) = toClause x nxt
                            (Clause cly,Formula fy,nxt2) = toClause y nxt1
                        in (Clause $ IntSet.union clx cly,Formula $ Set.union fx fy,nxt2)
toClause (Not (Atom v)) nxt = (Clause $ IntSet.singleton $ litId $ ln v,formulaEmpty,nxt)
toClause (Not (And x y)) nxt = toClause (Or (Not x) (Not y)) nxt
toClause f nxt = let (f',lit,nxt1) = tseitin f nxt
                 in (Clause $ IntSet.singleton $ litId lit,f',nxt1)

tseitin :: PropL Var -> Var -> (Formula,Lit,Var)
tseitin (Atom x) nxt = (formulaEmpty,lp x,nxt)
tseitin (Not x) nxt = let (f1,lit,nxt') = tseitin x nxt
                      in (f1,litNeg lit,nxt')
tseitin (And x y) nxt = let (Formula cnf_x,l1,nxt1) = tseitin x nxt
                            (Formula cnf_y,l2,nxt2) = tseitin y nxt1
                            Formula cnf_r = formulaAnd (lp nxt2) [l1,l2]
                        in (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],lp nxt2,succ nxt2)
tseitin (Or x y) nxt = let (Formula cnf_x,l1,nxt1) = tseitin x nxt
                           (Formula cnf_y,l2,nxt2) = tseitin y nxt1
                           Formula cnf_r = formulaOr (lp nxt2) [l1,l2]
                       in (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],lp nxt2,succ nxt2)
