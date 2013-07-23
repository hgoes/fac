module Main where

import Minisat
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,mapM_,foldl1)
import qualified Data.Set as Set
import Foreign.C
import Formula
import Aiger
import Literal
import Unrolling
import Simulator
import ProofBuilder
import Interpolation
import qualified Data.IntSet as IntSet
import System.Environment
import Data.Foldable
import Data.Proxy
import Data.Array.IO
import Data.Array (Array)
import Data.IORef

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
  builder <- newIORef (proofBuilder True)
  solverAddProofLog solver
    (\lits -> modifyIORef builder (proofBuilderRoot lits))
    (\nds vars -> modifyIORef builder (proofBuilderChain nds vars))
    (\nd -> modifyIORef builder (proofBuilderDelete nd))
    (return ())
  let nxt = solverNewVar solver
      assert (Formula f) = mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f
      chk = solverSolve solver
      model = solverGetModel solver
  (inp0,formula0,latch0) <- stepUnrolling nxt assert unrollment (Const False) (fmap (const (Const False)) (unrollLatches unrollment))
  let latch_vars0 = Set.unions $ fmap allVars (Map.elems latch0)
  modifyIORef builder (proofBuilderSetState False)
  res <- runUnrolling' nxt assert chk model unrollment formula0 latch0 ((read limit)-1)
  --res <- runUnrolling nxt assert chk model unrollment (read limit)
  case res of
    Nothing -> do
      putStrLn "No errors."
      proof <- readIORef builder
      putStr $ unlines $ renderProof (proofBuilderGet proof)
      print $ simplify $ interpolateProof HKP (flip Set.member latch_vars0) proof
      print latch_vars0
    Just (tr,_) -> do
      putStrLn "Error found:"
      putStr (unlines $ prettyTrace (\v -> getSymbolName v aiger_opt) tr)
      print $ simulateAiger aiger_opt tr
