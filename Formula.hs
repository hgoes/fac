module Formula where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List (intersperse)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Control.Applicative

newtype Literal = Literal { literalId :: Int } deriving (Eq,Ord)

instance Show Literal where
  showsPrec i = showsPrec i . literalId
  show = show . literalId
  showList = showList . map literalId

negateLiteral :: Literal -> Literal
negateLiteral = Literal . negate . literalId

-- | The 'False' constant. The literal @-1@ is dedicated for it.
literalFalse :: Literal
literalFalse = Literal (-1)

-- | The 'True' constant. The literal @1@ is dedicated for it.
literalTrue :: Literal
literalTrue = Literal 1

-- | A disjunction of possibly negated atoms. Negated atoms are represented
-- by negating the identifier.
newtype Clause = Clause { clauseSet :: IntSet }
  deriving (Eq, Ord, Monoid)

-- | Extract the (possibly negated) atoms referenced by a 'Clause'.
clauseLiterals :: Clause -> [Literal]
clauseLiterals (Clause is) = Literal <$> IntSet.toList is

-- | A conjunction of clauses
newtype Formula = Formula { formulaSet :: Set Clause }
  deriving (Eq, Ord, Monoid)

instance Show Formula where
  showsPrec p = showParen (p > 2) . foldr (.) id
              . List.intersperse (showString " & ") . map (showsPrec 3)
              . Set.toList . formulaSet

instance Show Clause where
  showsPrec p = showParen (p > 1) . foldr (.) id
              . List.intersperse (showString " | ") . map (showsPrec 2)
              . IntSet.toList . clauseSet


-- | A formula with no clauses
formulaEmpty :: Formula
formulaEmpty = Formula Set.empty

-- | Assert a literal
formulaLiteral :: Literal -> Formula
formulaLiteral (Literal l) =
  Formula (Set.singleton (Clause (IntSet.singleton l)))

-- | The boolean /not/ operation
--
-- Derivation of the Tseitin transformation:
--
-- @
-- O â‰¡ Â¬A
-- (O â†’ Â¬A) & (Â¬O â†’ A)
-- (Â¬O | Â¬A) & (O | A)
-- @
formulaNot :: Literal  -- ^ Output
           -> Literal  -- ^ Input
           -> Formula
formulaNot (Literal out) (Literal inp) = formulaFromList cls
  where
    cls = [ [-out, -inp], [out, inp] ]

-- | The boolean /and/ operation
--
-- Derivation of the Tseitin transformation:
--
-- @
-- O â‰¡ (A & B & C)
-- (O â†’ (A & B & C)) & (Â¬O â†’ Â¬(A & B & C))
-- (Â¬O | (A & B & C)) & (O | Â¬(A & B & C))
-- (Â¬O | A) & (Â¬O | B) & (Â¬O | C) & (O | Â¬A | Â¬B | Â¬C)
-- @
formulaAnd :: Literal    -- ^ Output
           -> [Literal]  -- ^ Inputs
           -> Formula
formulaAnd (Literal out) inpLs = formulaFromList cls
  where
    cls = (out : map negate inps) : map (\inp -> [-out, inp]) inps
    inps = map literalId inpLs

-- | The boolean /or/ operation
--
-- Derivation of the Tseitin transformation:
--
-- @
-- O â‰¡ (A | B | C)
-- (O â†’ (A | B | C)) & (Â¬O â†’ Â¬(A | B | C))
-- (Â¬O | (A | B | C)) & (O | Â¬(A | B | C))
-- (Â¬O | A | B | C) & (O | (Â¬A & Â¬B & Â¬C))
-- (Â¬O | A | B | C) & (O | Â¬A) & (O | Â¬B) & (O | Â¬C)
-- @
formulaOr :: Literal    -- ^ Output
          -> [Literal]  -- ^ Inputs
          -> Formula
formulaOr (Literal out) inpLs = formulaFromList cls
  where
    cls = (-out : inps)
        : map (\inp -> [out, -inp]) inps
    inps = map literalId inpLs

-- | The boolean /xor/ operation
--
-- Derivation of the Tseitin transformation:
--
-- @
-- O â‰¡ A âŠ• B
-- O â‰¡ ((Â¬A & B) | (A & Â¬B))
-- (O â†’ ((Â¬A & B) | (A & Â¬B))) & (Â¬O â†’ Â¬((Â¬A & B) | (A & Â¬B)))
-- @
--
-- Left hand side:
--
-- @
-- O â†’ ((Â¬A & B) | (A & Â¬B))
-- Â¬O | ((Â¬A & B) | (A & Â¬B))
-- Â¬O | ((Â¬A | A) & (Â¬A | Â¬B) & (A | B) & (Â¬B | B))
-- Â¬O | ((Â¬A | Â¬B) & (A | B))
-- (Â¬O | Â¬A | Â¬B) & (Â¬O | A | B)
-- @
--
-- Right hand side:
--
-- @
-- Â¬O â†’ Â¬((Â¬A & B) | (A & Â¬B))
-- O | Â¬((Â¬A & B) | (A & Â¬B))
-- O | (Â¬(Â¬A & B) & Â¬(A & Â¬B))
-- O | ((A | Â¬B) & (Â¬A | B))
-- (O | Â¬A | B) & (O | A | Â¬B)
-- @
--
-- Result:
--
-- @
-- (Â¬O | Â¬A | Â¬B) & (Â¬O | A | B) & (O | Â¬A | B) & (O | A | Â¬B)
-- @
formulaXor :: Literal  -- ^ Output
           -> Literal  -- ^ Input
           -> Literal  -- ^ Input
           -> Formula
formulaXor (Literal out) (Literal inpA) (Literal inpB) = formulaFromList cls
  where
    cls = [ [-out, -inpA, -inpB]
          , [-out,  inpA,  inpB]
          , [ out, -inpA,  inpB]
          , [ out,  inpA, -inpB]
          ]

-- | The boolean /else-then-if/ or /mux/ operation
--
-- Derivation of the Tseitin transformation:
--
-- @
-- O â‰¡ (F & Â¬P) | (T & P)
-- (O â†’ ((F & Â¬P) | (T & P))) & (Â¬O â†’ Â¬((F & Â¬P) | (T & P)))
-- @
--
-- Left hand side:
--
-- @
-- O â†’ ((F & Â¬P) | (T & P))
-- Â¬O | ((F & Â¬P) | (T & P))
-- Â¬O | ((F | T) & (F | P) & (T | Â¬P) & (Â¬P | P))
-- Â¬O | ((F | T) & (F | P) & (T | Â¬P))
-- (Â¬O | F | T) & (Â¬O | F | P) & (Â¬O | T | Â¬P)
-- @
--
-- Right hand side:
--
-- @
-- Â¬O â†’ Â¬((F & Â¬P) | (T & P))
-- O | Â¬((F & Â¬P) | (T & P))
-- O | (Â¬(F & Â¬P) & Â¬(T & P))
-- O | ((Â¬F | P) & (Â¬T | Â¬P))
-- (O | Â¬F | P) & (O | Â¬T | Â¬P)
-- @
--
-- Result:
--
-- @
-- (Â¬O | F | T) & (Â¬O | F | P) & (Â¬O | T | Â¬P) & (O | Â¬F | P) & (O | Â¬T | Â¬P)
-- @
formulaMux :: Literal  -- ^ Output
           -> Literal  -- ^ False branch
           -> Literal  -- ^ True branch
           -> Literal  -- ^ Predicate/selector
           -> Formula
formulaMux (Literal out) (Literal inpF) (Literal inpT) (Literal inpP) =
  formulaFromList cls
  where
    cls = [ [-out,  inpF,  inpT]
          , [-out,  inpF,  inpP]
          , [-out,  inpT, -inpP]
          , [ out, -inpF,  inpP]
          , [ out, -inpT, -inpP]
          ]

formulaFromList :: [[Int]] -> Formula
formulaFromList = Formula . Set.fromList . map (Clause . IntSet.fromList)

data PropL var
  = Atom var
  | Not (PropL var)
  | And (PropL var) (PropL var)
  | Or (PropL var) (PropL var)

toCNF :: PropL Int -> Int -> (Formula,Int)
toCNF (Atom v) nxt = (formulaLiteral $ Literal v,nxt)
toCNF (And x y) nxt = let (fx,nxt1) = toCNF x nxt
                          (fy,nxt2) = toCNF y nxt1
                      in (Formula $ Set.union (formulaSet fx) (formulaSet fy),nxt2)
toCNF (Or x y) nxt = let (Clause clx,Formula fx,nxt1) = toClause x nxt
                         (Clause cly,Formula fy,nxt2) = toClause y nxt1
                     in (Formula $ Set.insert (Clause $ IntSet.union clx cly) (Set.union fx fy),nxt2)
toCNF (Not (Not x)) nxt = toCNF x nxt
toCNF (Not (Atom v)) nxt = (formulaLiteral $ negateLiteral $ Literal v,nxt)
toCNF (Not (Or x y)) nxt = toCNF (And (Not x) (Not y)) nxt
toCNF (Not (And x y)) nxt = toCNF (Or (Not x) (Not y)) nxt

toClause :: PropL Int -> Int -> (Clause,Formula,Int)
toClause (Atom v) nxt = (Clause $ IntSet.singleton v,formulaEmpty,nxt)
toClause (Or x y) nxt = let (Clause clx,Formula fx,nxt1) = toClause x nxt
                            (Clause cly,Formula fy,nxt2) = toClause y nxt1
                        in (Clause $ IntSet.union clx cly,Formula $ Set.union fx fy,nxt2)
toClause (Not (Atom v)) nxt = (Clause $ IntSet.singleton (-v),formulaEmpty,nxt)
toClause (Not (And x y)) nxt = toClause (Or (Not x) (Not y)) nxt
toClause f nxt = let (f',lit,nxt1) = tseitin f nxt
                 in (Clause $ IntSet.singleton $ literalId lit,f',nxt1)

tseitin :: PropL Int -> Int -> (Formula,Literal,Int)
tseitin (Atom x) nxt = (formulaEmpty,Literal x,nxt)
tseitin (Not x) nxt = let (f1,lit,nxt') = tseitin x nxt
                      in (f1,negateLiteral lit,nxt')
tseitin (And x y) nxt = let (Formula cnf_x,l1,nxt1) = tseitin x nxt
                            (Formula cnf_y,l2,nxt2) = tseitin y nxt1
                            Formula cnf_r = formulaAnd (Literal nxt2) [l1,l2]
                        in (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],Literal nxt2,succ nxt2)
tseitin (Or x y) nxt = let (Formula cnf_x,l1,nxt1) = tseitin x nxt
                           (Formula cnf_y,l2,nxt2) = tseitin y nxt1
                           Formula cnf_r = formulaOr (Literal nxt2) [l1,l2]
                       in (Formula $ Set.unions [cnf_x,cnf_y,cnf_r],Literal nxt2,succ nxt2)
