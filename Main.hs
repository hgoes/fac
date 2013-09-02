module Main where

import Minisat
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,mapM,mapM_,foldl1,any,or)
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
import Data.Traversable

prettyTrace :: (Var -> Maybe String) -> [Map Var Bool] -> [String]
prettyTrace mp steps = prettyTrace' steps 1
  where
    prettyTrace' [] _ = []
    prettyTrace' (step:steps) n = ("Step "++show n):
                                  [ "|- "++(case mp var of
                                               Nothing -> show var
                                               Just sym -> sym)++" = "++show val
                                  | (var,val) <- Map.toList step ]++(prettyTrace' steps (n+1))

verify :: AigerC aiger => aiger -> Unrolling -> PropL Var -> Int -> IO (Maybe [Map Var Bool])
verify aiger unrollment latch_f depth = do
  putStrLn $ "Depth: "++show depth
  solver <- solverNew
  builder <- newIORef (proofBuilder True)
  solverAddProofLog solver
    (\lits -> {-putStrLn ("Add proof root: "++show lits) >> -} modifyIORef builder (proofBuilderRoot lits))
    (\nds vars -> modifyIORef builder (proofBuilderChain nds vars))
    (\nd -> modifyIORef builder (proofBuilderDelete nd))
    (return ())
  (latches,latch_f') <- encodeFormula solver latch_f Map.empty
  -- Add free variables to latches:
  latches_free <- mapM (const $ solverNewVar solver) (Map.difference (unrollLatches unrollment) latches)
  let latches' = Map.union latches latches_free
      nxt = solverNewVar solver
      assert (Formula f) = do
        --putStrLn $ "Assert "++show (Formula f)
        mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f
      chk = solverSolve solver
      model = solverGetModel solver
      step c = if c==1
               then {-putStrLn "Switch" >>-} modifyIORef builder (proofBuilderSetState False)
               else return ()
  res <- runUnrolling nxt assert step chk model unrollment depth latch_f' latches'
  solverDelete solver
  case res of
    Left tr -> if any or $ simulateAiger aiger tr
               then return (Just tr) -- The trace is a real error
               else verify aiger unrollment
                    (if Map.null (unrollLatches unrollment)
                     then Const True
                     else foldl1 And [ Not (Atom latch) | latch <- Map.keys (unrollLatches unrollment) ])
                    (depth+1)
    Right ((_,slatch):_) -> do
      let latch_vars = Set.fromList $ Map.elems (fmap litVar slatch)
      proof <- readIORef builder
      --putStr $ unlines $ renderProof (proofBuilderGet proof)
      let interpolant = simplify $ interpolateProof McMillan (flip Set.member latch_vars) proof
      --print interpolant
      --print $ Map.elems slatch
      --print $ Map.elems latches'
      let dec_interp = decodeFormula (Map.fromList [ (litVar v2,v1) | (v1,v2) <- Map.toList slatch ]) interpolant
      --print dec_interp
      sat <- checkSat (And (Not latch_f) dec_interp)
      if sat
        then verify aiger unrollment dec_interp depth -- The interpolant changed, repeat
        else return Nothing -- We found a fixpoint, no error exists
  
  where
    encodeFormula :: Ord a => Solver -> PropL a -> Map a Var -> IO (Map a Var,PropL Var)
    encodeFormula _ (Const c) mp = return (mp,Const c)
    encodeFormula solver (Atom v) mp = case Map.lookup v mp of
      Nothing -> do
        nv <- solverNewVar solver
        return (Map.insert v nv mp,Atom nv)
      Just r -> return (mp,Atom r)
    encodeFormula solver (Not f) mp = do
      (mp',f') <- encodeFormula solver f mp
      return (mp',Not f')
    encodeFormula solver (And x y) mp = do
      (mp1,x') <- encodeFormula solver x mp
      (mp2,y') <- encodeFormula solver y mp1
      return (mp2,And x' y')
    encodeFormula solver (Or x y) mp = do
      (mp1,x') <- encodeFormula solver x mp
      (mp2,y') <- encodeFormula solver y mp1
      return (mp2,Or x' y')

    decodeFormula :: Show a => Map Var a -> PropL Var -> PropL a
    decodeFormula _ (Const c) = Const c
    decodeFormula mp (Atom v) = case Map.lookup v mp of
      Just r -> Atom r
      Nothing -> error $ "Failed to decode "++show v++" "++show mp
    decodeFormula mp (Not f) = Not $ decodeFormula mp f
    decodeFormula mp (And x y) = And (decodeFormula mp x) (decodeFormula mp y)
    decodeFormula mp (Or x y) = Or (decodeFormula mp x) (decodeFormula mp y)

    checkSat :: PropL Var -> IO Bool
    checkSat f = do
      --putStrLn $ "Check "++show f++" for sat"
      solver <- solverNew
      (_,f') <- encodeFormula solver f Map.empty
      (Formula f_cnf) <- toCNF (solverNewVar solver) f'
      mapM_ (\cl -> solverAddClause solver (clauseLits cl)) f_cnf
      res <- solverSolve solver
      --putStrLn $ "Result is "++(if res then "SAT" else "UNSAT")
      solverDelete solver
      return res

main = do
  [file] <- getArgs
  aiger_str <- readFile file
  let aiger = readAiger aiger_str :: Aiger Lit
      aiger_opt = optimizeAiger aiger
      unrollment = buildUnrolling aiger_opt (countUses aiger_opt)
  --print unrollment
  res <- verify aiger_opt unrollment (if Map.null (unrollLatches unrollment)
                                      then Const True
                                      else foldl1 And [ Not (Atom latch) | latch <- Map.keys (unrollLatches unrollment) ]) 2
  case res of
    Just tr -> do
      putStrLn "Error found:"
      putStr (unlines $ prettyTrace (\v -> getSymbolName v aiger_opt) tr)
      print $ simulateAiger aiger_opt tr
    Nothing -> putStrLn "No errors."
