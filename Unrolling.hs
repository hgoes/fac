module Unrolling where

import Aiger
import Literal
import Formula

import Data.Foldable
import qualified Data.List as List
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,foldl1)

import Debug.Trace

formulaForGate :: (Monad m,Literal gate,Ord gate) => m Var -> (Formula -> m ()) -> Aiger gate -> Map Var Int -> Map gate (PropL Var) -> gate -> m (PropL Var,Map gate (PropL Var))
formulaForGate nxt assert aiger num_uses mp gate = case Map.lookup gate mp of -- Did we already translate this gate?
  -- Yes, great, return it.
  Just fgate -> return (fgate,mp)
  -- No. Maybe we have translated its negation?
  Nothing -> case Map.lookup (litNeg gate) mp of
    -- Yes, great, negate it and return it.
    Just fgate -> return (Not fgate,Map.insert gate (Not fgate) mp)
    -- No.
    Nothing -> do
      -- Looks like we actually have to do some work...
      let (in1,in2) = getGate (litVar gate) aiger
      (f1,mp1) <- formulaForGate nxt assert aiger num_uses mp in1
      (f2,mp2) <- formulaForGate nxt assert aiger num_uses mp1 in2

      --trace ((if litSign gate then "" else "!") ++ show f1 ++ " && " ++ show f2) (return ())

      let rf = simplify $ if litSign gate
                          then And f1 f2
                          else Not (And f1 f2)
      --trace (" => " ++ show rf) (return ())
      
      -- Is the resulting formula very simple?
      case rf of
        Const x -> return (rf,Map.insert gate rf mp2)
        Atom v -> return (rf,Map.insert gate rf mp2)
        (Not (Atom v)) -> return (rf,Map.insert gate rf mp2)
        -- How many times is the output of the gate used?
        _ -> case Map.lookup (litVar gate) num_uses of
          -- Yay, only once, we don't have to introduce a new variable
          Just 1 -> do
            return (rf,Map.insert gate rf mp2)
          -- It is used more than once, so we have to introduce a new variable.
          _ -> do
            (rf',rlit) <- tseitin nxt rf
            -- Assert the resulting formula
            assert rf'
            let res = if litSign rlit
                      then Atom (litVar rlit)
                      else Not (Atom (litVar rlit))
            return (res,Map.insert gate res mp2)

stepSystem :: (Monad m,Literal gate,Ord gate) => m Var -> (Formula -> m ()) -> Aiger gate -> Map Var Int -> Map gate (PropL Var) -> m (Map gate (PropL Var),Map gate (PropL Var),Map gate (PropL Var))
stepSystem nxt assert aiger num_uses mp = do
  ninps <- foldlM (\inp_map inp -> do
                      var <- nxt
                      let res = if litSign inp
                                then Atom var
                                else Not (Atom var)
                      return (Map.insert inp res inp_map)
                  ) Map.empty (aigerInputs aiger)
  (mp1,nlatches) <- foldlM (\(cmp,latch_map) (latch_to,latch_from) -> do
                               (f_from,nmp) <- formulaForGate nxt assert aiger num_uses cmp latch_from
                               return (nmp,Map.insert latch_to f_from latch_map)
                           ) (Map.union mp ninps,Map.empty) (aigerLatches aiger)
  (mp2,noutp) <- foldlM (\(cmp,outp_map) outp -> do
                            (f_outp,nmp) <- formulaForGate nxt assert aiger num_uses cmp outp
                            return (nmp,Map.insert outp f_outp outp_map)
                        ) (mp1,Map.empty) (aigerOutputs aiger)
  return (ninps,nlatches,noutp)

initialValues :: Ord gate => Aiger gate -> Map gate (PropL Var)
initialValues aiger = foldl (\cmp (latch,_) -> Map.insert latch (Const False) cmp) Map.empty (aigerLatches aiger)

data Unrollment m gate = Unrollment { unrollmentNewVar :: m Var
                                    , unrollmentAssert :: Formula -> m ()
                                    , unrollmentCheck :: [(Var,Bool)] -> m Bool
                                    , unrollmentGetModel :: m [Bool]
                                    , unrollmentModel :: Aiger gate
                                    , unrollmentUses :: Map Var Int
                                    , unrollmentInputs :: [Map gate (PropL Var)]
                                    , unrollmentLatches :: [Map gate (PropL Var)]
                                    , unrollmentOutputs :: [Map gate (PropL Var)]
                                    }

initialUnrollment :: (Literal gate,Ord gate) => m Var -> (Formula -> m ()) -> ([(Var,Bool)] -> m Bool) -> m [Bool] -> Aiger gate -> Unrollment m gate
initialUnrollment nxt assert check model aiger
  = Unrollment { unrollmentNewVar = nxt
               , unrollmentAssert = assert
               , unrollmentCheck = check
               , unrollmentGetModel = model
               , unrollmentModel = aiger
               , unrollmentUses = countUses aiger
               , unrollmentInputs = []
               , unrollmentLatches = [initialValues aiger]
               , unrollmentOutputs = []
               }

stepUnrollment :: (Monad m,Literal gate,Ord gate) => Unrollment m gate -> m (Unrollment m gate)
stepUnrollment unroll = do
  (ninp,nlatch,nout) <- stepSystem (unrollmentNewVar unroll) (unrollmentAssert unroll) (unrollmentModel unroll) (unrollmentUses unroll) (head $ unrollmentLatches unroll)
  return $ unroll { unrollmentInputs = ninp:(unrollmentInputs unroll)
                  , unrollmentLatches = nlatch:(unrollmentLatches unroll)
                  , unrollmentOutputs = nout:(unrollmentOutputs unroll)
                  }

checkUnrollment :: Monad m => Unrollment m gate -> m (Maybe [Map gate Bool])
checkUnrollment unroll = do
  let cond = simplify $ foldl1 Or [ f | outp <- unrollmentOutputs unroll, f <- Map.elems outp ]
  cond_cnf <- toCNF (unrollmentNewVar unroll) cond
  unrollmentAssert unroll cond_cnf
  res <- unrollmentCheck unroll []
  if res
    then (do
             model <- unrollmentGetModel unroll
             return $ Just $ fmap (fmap (\var -> case var of
                                            Atom v -> List.genericIndex model v
                                            Not (Atom v) -> not $ List.genericIndex model v
                                        )) (unrollmentInputs unroll))
    else return Nothing