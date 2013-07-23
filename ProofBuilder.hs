module ProofBuilder where

import Literal
import Formula

import Data.Map (Map,(!))
import qualified Data.Map as Map
import Data.IORef
import Foreign.C
import qualified Data.IntSet as IntSet
import Data.List
import Data.Ord

data ProofNode a = ProofRoot Clause a
                 | ProofChain [ProofNode a] [Var]
                 deriving Show

data ProofBuilder a = ProofBuilder { proofNodes :: Map CInt (ProofNode a)
                                   , proofState :: a
                                   , nextNode :: CInt }

proofBuilder :: a -> ProofBuilder a
proofBuilder def = ProofBuilder Map.empty def 0

proofBuilderSetState :: a -> ProofBuilder a -> ProofBuilder a
proofBuilderSetState st builder = builder { proofState = st }

proofBuilderRoot :: [Lit] -> ProofBuilder a -> ProofBuilder a
proofBuilderRoot lits builder = builder { proofNodes = Map.insert (nextNode builder) (ProofRoot (Clause $ IntSet.fromList $ fmap litId lits) (proofState builder)) (proofNodes builder)
                                        , nextNode = succ (nextNode builder)
                                        }

proofBuilderChain :: [CInt] -> [Var] -> ProofBuilder a -> ProofBuilder a
proofBuilderChain cls vars builder = let cls' = fmap ((proofNodes builder)!) cls
                                     in builder { proofNodes = Map.insert (nextNode builder) (ProofChain cls' vars) (proofNodes builder)
                                                , nextNode = succ (nextNode builder)
                                                }

proofBuilderDelete :: CInt -> ProofBuilder a -> ProofBuilder a
proofBuilderDelete cl builder = builder { proofNodes = Map.delete cl (proofNodes builder) }

proofBuilderGet :: ProofBuilder a -> ProofNode a
proofBuilderGet builder = (proofNodes builder)!(pred $ nextNode builder)

renderProof :: Show a => ProofNode a -> [String]
renderProof (ProofRoot cl ann) = [show cl++" ["++show ann++"]"]
renderProof (ProofChain nds vars) = proofs_with_vars
  where
    proofs = fmap renderProof nds
    heighest = maximum (fmap length proofs)
    proofs' = fmap (adaptHeight heighest) proofs

    conc_proofs = hcat (intersperse (replicate heighest "  ") proofs')

    line_width = length $ head conc_proofs

    line_proofs = conc_proofs ++ [replicate line_width '-']

    elim_vars = concat $ intersperse "," (fmap show vars)
    vars_width = length elim_vars

    proofs_with_vars = hcat [line_proofs,(replicate heighest (replicate vars_width  ' '))++[elim_vars]]
    
    adaptHeight h xs = let h' = length xs
                           w = length $ head xs
                       in replicate (h-h') (replicate w ' ') ++ xs
    hcat [] = []
    hcat ([]:_) = []
    hcat xs = (concat $ fmap head xs):(hcat (fmap tail xs))

{-
proofVerify :: ProofNode -> Clause
proofVerify (ProofRoot cl) = cl
proofVerify (ProofChain cls vars)
  = Clause $ foldl (\cset var -> IntSet.delete (litId $ lp var) $
                                 IntSet.delete (litId $ ln var) $
                                 cset
                   ) (IntSet.unions $ fmap (\(Clause cl) -> cl) (fmap proofVerify cls)) vars
-}
