module Unrolling where

import Aiger
import Literal
import Formula

import Data.Foldable
import qualified Data.List as List
import Data.Map.Strict as Map hiding (foldl)
import Prelude hiding (foldl,foldl1)

data UnrollAction = PushInput Var
                  | PushLatch Var
                  | PushFormula (PropL Int)
                  deriving (Show)

data Unrolling = Unrolling { unrollmentActions :: [UnrollAction]
                           , unrollInputs :: Map Var Int
                           , unrollLatches :: Map Var (Int,Bool)
                           , unrollOutputs :: Map Var (PropL Int)
                           , unrollLatchesOut :: Map Var (PropL Int)
                           , unrollStackSize :: Int }
                 deriving (Show)

buildUnrolling :: (AigerC aiger) => aiger -> Map Var Int -> Unrolling
buildUnrolling aiger num_uses = Unrolling { unrollmentActions = act2++act1
                                          , unrollInputs = inp_mp2
                                          , unrollLatches = latch_mp2
                                          , unrollOutputs = outp_mp
                                          , unrollLatchesOut = latch_out_mp
                                          , unrollStackSize = off2
                                          }
    where
      (inp_mp1,latch_mp1,outp_mp,mp1,act1,off1)
        = foldl (\(cinp_mp,clatch_mp,coutp_mp,cmp,cact,coff) outp
                 -> let (f,noff,nact,ninp_mp,nlatch_mp,nmp) = actionForGate outp cinp_mp clatch_mp cmp coff
                    in (ninp_mp,nlatch_mp,Map.insert outp f coutp_mp,nmp,nact++cact,noff)
                ) (Map.empty,Map.empty,Map.empty,Map.empty,[],0) (aigerOutputs aiger)
      (inp_mp2,latch_mp2,latch_out_mp,mp2,act2,off2)
        = foldl (\(cinp_mp,clatch_mp,clatch_out_mp,cmp,cact,coff) (latch_out,latch_pos,latch_from)
                 -> let (f,noff,nact,ninp_mp,nlatch_mp,nmp) = actionForGate latch_from cinp_mp clatch_mp cmp coff
                    in (ninp_mp,nlatch_mp,Map.insert latch_out (if latch_pos
                                                                then f
                                                                else Not f) clatch_out_mp,nmp,nact++cact,noff)
                ) (inp_mp1,latch_mp1,Map.empty,mp1,[],off1) (aigerLatches aiger)

      actionForGate :: Var -> Map Var Int -> Map Var (Int,Bool) -> Map Var (PropL Int) -> Int -> (PropL Int,Int,[UnrollAction],Map Var Int,Map Var (Int,Bool),Map Var (PropL Int))
      actionForGate gate inp_mp latch_mp mp off = case Map.lookup gate mp of
        Just f -> (f,off,[],inp_mp,latch_mp,mp)
        Nothing -> case getSymbol gate aiger of
          Input -> (Atom off,off+1,[PushInput gate],Map.insert gate off inp_mp,latch_mp,Map.insert gate (Atom off) mp)
          Latch -> let (latch_from,latch_pos) = getLatch gate aiger
                   in (Atom off,off+1,[PushLatch gate],inp_mp,Map.insert latch_from (off,latch_pos) latch_mp,Map.insert gate (Atom off) mp)
          Gate -> let (gl,pl,gr,pr) = getGate gate aiger
                      (fl,off1,act_l,inp_mp1,latch_mp1,mp1) = actionForGate gl inp_mp latch_mp mp off
                      (fr,off2,act_r,inp_mp2,latch_mp2,mp2) = actionForGate gr inp_mp1 latch_mp1 mp1 off1
                      f = simplify $ And (if pl then fl else Not fl) (if pr then fr else Not fr)
                  in case Map.lookup gate num_uses of
                    Just 1 -> (f,off2,act_r++act_l,inp_mp2,latch_mp2,Map.insert gate (simplify $ And fl fr) mp2)
                    Just _ -> (Atom off2,off2+1,[PushFormula f]++act_r++act_l,inp_mp2,latch_mp2,Map.insert gate (Atom off2) mp2)

formulaForGate :: (Monad m,AigerC aiger) => m Var -> (Formula -> m ()) -> aiger -> Map Var Int -> Map Var (PropL Var) -> Var -> Bool -> m (PropL Var,Map Var (PropL Var))
formulaForGate nxt assert aiger num_uses mp gate gpos = case Map.lookup gate mp of -- Did we already translate this gate?
  -- Yes, great, return it.
  Just fgate -> return (if gpos
                        then fgate
                        else (case fgate of
                                 Not f -> f
                                 _ -> Not fgate),mp)
  -- No.
  Nothing -> case getSymbol gate aiger of
    Gate -> do
      --trace ("Get gate "++show gate) (return ())
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