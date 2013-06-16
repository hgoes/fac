module Unrolling where

import Aiger
import Literal
import Formula

import Data.Foldable
import qualified Data.List as List
import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,foldl1)

formulaForGate :: (Monad m,AigerC aiger) => m Var -> (Formula -> m ()) -> aiger -> Map Var Int -> Map Var (PropL Var) -> Var -> Bool -> m (PropL Var,Map Var (PropL Var))
formulaForGate nxt assert aiger num_uses mp gate gpos = case Map.lookup gate mp of -- Did we already translate this gate?
  -- Yes, great, return it.
  Just fgate -> if gpos
                then return (fgate,mp)
                else (case fgate of
                         Not f -> return (f,mp)
                         _ -> return (Not fgate,mp))
  -- No.
  Nothing -> do
    -- Looks like we actually have to do some work...
    let (in1,pos1,in2,pos2) = getGate gate aiger
    (f1,mp1) <- formulaForGate nxt assert aiger num_uses mp in1 pos1
    (f2,mp2) <- formulaForGate nxt assert aiger num_uses mp1 in2 pos2
    let rf = simplify $ if gpos
                        then And f1 f2
                        else Not $ And f1 f2
      -- Is the resulting formula very simple?
    case rf of
        Const x -> return (rf,Map.insert gate rf mp2)
        Atom v -> return (rf,Map.insert gate rf mp2)
        (Not (Atom v)) -> return (rf,Map.insert gate rf mp2)
        -- How many times is the output of the gate used?
        _ -> case Map.lookup gate num_uses of
          -- Yay, only once, we don't have to introduce a new variable
          Just 1 -> do
            return (rf,Map.insert gate rf mp2)
          -- It is used more than once, so we have to introduce a new variable.
          _ -> do
            (rf',rlit) <- tseitin nxt rf
            -- Assert the resulting formula
            assert rf'
            let res = if litIsP rlit
                      then Atom (litVar rlit)
                      else Not (Atom (litVar rlit))
            return (res,Map.insert gate res mp2)

stepSystem :: (Monad m,AigerC aiger) => m Var -> (Formula -> m ()) -> aiger -> Map Var Int -> Map Var (PropL Var) -> m (Map Var (PropL Var),Map Var (PropL Var),Map Var (PropL Var))
stepSystem nxt assert aiger num_uses mp = do
  ninps <- foldlM (\inp_map inp -> do
                      var <- nxt
                      let res = Atom var
                      return (Map.insert inp res inp_map)
                  ) Map.empty (aigerInputs aiger)
  (mp1,nlatches) <- foldlM (\(cmp,latch_map) (latch_to,latch_pos,latch_from) -> do
                               (f_from,nmp) <- formulaForGate nxt assert aiger num_uses cmp latch_from latch_pos
                               return (nmp,Map.insert latch_to f_from latch_map)
                           ) (Map.union mp ninps,Map.empty) (aigerLatches aiger)
  (mp2,noutp) <- foldlM (\(cmp,outp_map) outp -> do
                            (f_outp,nmp) <- formulaForGate nxt assert aiger num_uses cmp outp True
                            return (nmp,Map.insert outp f_outp outp_map)
                        ) (mp1,Map.empty) (aigerOutputs aiger)
  return (ninps,nlatches,noutp)

initialValues :: AigerC aiger => aiger -> Map Var (PropL Var)
initialValues aiger = foldl (\cmp (latch,_,_) -> Map.insert latch (Const False) cmp) Map.empty (aigerLatches aiger)

data Unrollment m aiger = Unrollment { unrollmentNewVar :: m Var
                                     , unrollmentAssert :: Formula -> m ()
                                     , unrollmentCheck :: [(Var,Bool)] -> m Bool
                                     , unrollmentGetModel :: m [Bool]
                                     , unrollmentModel :: aiger
                                     , unrollmentUses :: Map Var Int
                                     , unrollmentInputs :: [Map Var (PropL Var)]
                                     , unrollmentLatches :: [Map Var (PropL Var)]
                                     , unrollmentOutputs :: [Map Var (PropL Var)]
                                     }

initialUnrollment :: AigerC aiger => m Var -> (Formula -> m ()) -> ([(Var,Bool)] -> m Bool) -> m [Bool] -> aiger -> Unrollment m aiger
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

stepUnrollment :: (Monad m,AigerC aiger) => Unrollment m aiger -> m (Unrollment m aiger)
stepUnrollment unroll = do
  (ninp,nlatch,nout) <- stepSystem (unrollmentNewVar unroll) (unrollmentAssert unroll) (unrollmentModel unroll) (unrollmentUses unroll) (head $ unrollmentLatches unroll)
  return $ unroll { unrollmentInputs = ninp:(unrollmentInputs unroll)
                  , unrollmentLatches = nlatch:(unrollmentLatches unroll)
                  , unrollmentOutputs = nout:(unrollmentOutputs unroll)
                  }

getFormulaValue :: PropL Var -> [Bool] -> Bool
getFormulaValue (Const x) mdl = x
getFormulaValue (Atom v) mdl = List.genericIndex mdl v
getFormulaValue (Not f) mdl = not $ getFormulaValue f mdl
getFormulaValue (And x y) mdl = (getFormulaValue x mdl) && (getFormulaValue y mdl)
getFormulaValue (Or x y) mdl = (getFormulaValue x mdl) || (getFormulaValue y mdl)

checkUnrollment :: (Monad m,AigerC aiger) => Unrollment m aiger -> m (Maybe [Map Var Bool])
checkUnrollment unroll = do
  let cond = simplify $ foldl1 Or [ f | outp <- unrollmentOutputs unroll, f <- Map.elems outp ]
  cond_cnf <- toCNF (unrollmentNewVar unroll) cond
  unrollmentAssert unroll cond_cnf
  res <- unrollmentCheck unroll []
  if res
    then (do
             model <- unrollmentGetModel unroll
             return $ Just [ Map.fromList [ (gate,getFormulaValue f model)
                                          | (gate,f) <- Map.toList inp_mp ]
                           | inp_mp <- unrollmentInputs unroll ])
    else return Nothing