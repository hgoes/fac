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

prettyTrace :: (Var -> Maybe String) -> [Map Var Bool] -> [String]
prettyTrace mp steps = prettyTrace' steps 1
  where
    prettyTrace' [] _ = []
    prettyTrace' (step:steps) n = ("Step "++show n):
                                  [ "|- "++(case mp var of
                                               Nothing -> show var
                                               Just sym -> sym)++" = "++show val
                                  | (var,val) <- Map.toList step ]++(prettyTrace' steps (n+1))

main = do
  [file,limit] <- getArgs
  aiger_str <- readFile file
  let aiger = readAiger aiger_str :: Aiger Lit
      aiger_opt = optimizeAiger aiger
      unrollment = buildUnrolling aiger_opt (countUses aiger_opt)
  solver <- solverNew
  let nxt = solverNewVar solver
      assert (Formula f) = mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f
      chk = solverSolve solver
      model = solverGetModel solver
  res <- runUnrolling nxt assert chk model unrollment (read limit)
  case res of
    Nothing -> putStrLn "No errors."
    Just tr -> do
      putStrLn "Error found:"
      putStr (unlines $ prettyTrace (\v -> getSymbolName v aiger_opt) tr)