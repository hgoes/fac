module Main where

import Minisat
import Data.IORef
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,mapM_)
import Foreign.C
import Formula
import Aiger
import Literal
import Unrolling
import Simulator
import qualified Data.IntSet as IntSet
import System.Environment
import Data.Foldable

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
  solver <- solverNew
  let init = initialUnrollment
             (solverNewVar solver)
             (\(Formula f) -> mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f)
             (\vars -> solverSolveWith solver [ lit var sgn | (var,sgn) <- vars ])
             (solverGetModel solver)
             aiger
  last <- foldlM (\cur _ -> stepUnrollment cur) init [1..(read limit)]
  res <- checkUnrollment last
  case res of
    Nothing -> putStrLn "No errors found."
    Just cex -> do
      putStrLn $ "Counterexample: "++show cex
      print $ simulateAiger aiger cex