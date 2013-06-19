module Main where

import Minisat
import Data.IORef
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,mapM_,foldl1)
import Foreign.C
import Formula
import Aiger
import Literal
import Unrolling
import Simulator
import qualified Data.IntSet as IntSet
import System.Environment
import Data.Foldable
import Data.Proxy
import Data.Array.IO
import Data.Array (Array)

data ProofNode = ProofRoot Clause
               | ProofChain [ProofNode] [Var]
               deriving Show

data ProofBuilder = ProofBuilder { proofNodes :: Map CInt ProofNode
                                 , nextNode :: CInt }

proofBuilder :: ProofBuilder
proofBuilder = ProofBuilder Map.empty 0

proofBuilderRoot :: [Lit] -> ProofBuilder -> ProofBuilder
proofBuilderRoot lits builder = builder { proofNodes = Map.insert (nextNode builder) (ProofRoot $ Clause $ IntSet.fromList $ fmap litId lits) (proofNodes builder)
                                        , nextNode = succ (nextNode builder)
                                        }

proofBuilderChain :: [CInt] -> [Var] -> ProofBuilder -> ProofBuilder
proofBuilderChain cls vars builder = let cls' = fmap ((proofNodes builder)!) cls
                                     in builder { proofNodes = Map.insert (nextNode builder) (ProofChain cls' vars) (proofNodes builder)
                                                , nextNode = succ (nextNode builder)
                                                }

proofBuilderDelete :: CInt -> ProofBuilder -> ProofBuilder
proofBuilderDelete cl builder = builder { proofNodes = Map.delete cl (proofNodes builder) }

proofBuilderGet :: ProofBuilder -> ProofNode
proofBuilderGet builder = (proofNodes builder)!(pred $ nextNode builder)

proofVerify :: ProofNode -> Clause
proofVerify (ProofRoot cl) = cl
proofVerify (ProofChain cls vars)
  = Clause $ foldl (\cset var -> IntSet.delete (litId $ lp var) $
                                 IntSet.delete (litId $ ln var) $
                                 cset
                   ) (IntSet.unions $ fmap (\(Clause cl) -> cl) (fmap proofVerify cls)) vars

main = do
  [file,limit] <- getArgs
  aiger_str <- readFile file
  let aiger = readAiger aiger_str :: Aiger Lit
      aiger_opt = optimizeAiger aiger
      unrollment = buildUnrolling aiger_opt (countUses aiger_opt)
  solver <- solverNew
  let nxt = solverNewVar solver
      assert (Formula f) = {-putStrLn ("Asserting "++show f) >>-} mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f
  (assertion,_) <- foldlM (\(cf,clatch) i -> do
                              (arr::Array Int Int) <- performUnrolling (Proxy :: Proxy IOArray) 
                                                      nxt
                                                      assert
                                                      unrollment
                                                      clatch
                              let fs = foldl (\f outp -> Or f (unrollingGetValue outp arr)) (Const False) (unrollOutputs unrollment)
                                  nlatch = fmap (\(latch_f) -> unrollingGetValue latch_f arr
                                                ) (unrollLatchesOut unrollment)
                              return (Or cf fs,nlatch)
                          ) (Const False,fmap (const $ Const False) (unrollLatches unrollment)) [1..(read limit)]
  let simpl_assertion = simplify assertion
  cnf_assertion <- toCNF nxt simpl_assertion
  assert cnf_assertion
  res <- solverSolve solver
  if res
    then putStrLn "Error found."
    else putStrLn "No errors found."