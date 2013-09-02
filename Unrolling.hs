module Unrolling where

import Aiger
import Literal
import Formula

import Data.Foldable
import qualified Data.List as List
import Data.Map.Strict as Map hiding (foldl,(!))
import Prelude hiding (foldl,foldl1,mapM,sequence)
import Data.Traversable
import Data.Array.MArray.Safe
import Data.Array.IO (IOArray)
import Data.Array.Unboxed
import Data.Array.Unsafe
import Data.Proxy

data UnrollAction = PushInput Var
                  | PushLatch Var
                  | PushFormula (PropL Int)
                  deriving (Show)

data Unrolling = Unrolling { unrollmentActions :: [UnrollAction]
                           , unrollInputs :: Map Var Int
                           , unrollLatches :: Map Var (Int,Var,Bool)
                           , unrollOutputs :: Map Var (PropL Int)
                           , unrollLatchesOut :: Map Var (Int,Var,Bool)
                           , unrollStackSize :: Int }
                 deriving (Show)

buildUnrolling :: (AigerC aiger) => aiger -> Map Var Int -> Unrolling
buildUnrolling aiger num_uses = Unrolling { unrollmentActions = reverse $ act2++act1
                                          , unrollInputs = inp_mp2
                                          , unrollLatches = latch_mp2
                                          , unrollOutputs = outp_mp
                                          , unrollLatchesOut = latch_out_mp
                                          , unrollStackSize = off2
                                          }
    where
      (inp_mp1,latch_mp1,outp_mp,mp1,act1,off1)
        = foldl (\(cinp_mp,clatch_mp,coutp_mp,cmp,cact,coff) outp
                 -> let (f,noff,nact,ninp_mp,nlatch_mp,nmp) = actionForGate (litVar outp) cinp_mp clatch_mp cmp coff
                        f' = if litIsP outp
                             then f
                             else Not f
                    in (ninp_mp,nlatch_mp,Map.insert (litVar outp) f' coutp_mp,nmp,nact++cact,noff)
                ) (Map.empty,Map.empty,Map.empty,Map.empty,[],0) (aigerOutputs aiger)
      (inp_mp2,latch_mp2,latch_out_mp,mp2,act2,off2)
        = foldl (\(cinp_mp,clatch_mp,clatch_out_mp,cmp,cact,coff) (latch_out,latch_pos,latch_from)
                 -> let (f,noff,nact,ninp_mp,nlatch_mp,nmp) = actionForGate latch_from cinp_mp clatch_mp cmp coff
                    in (ninp_mp,nlatch_mp,Map.insert latch_out (noff,latch_from,latch_pos) clatch_out_mp,nmp,[PushFormula f]++nact++cact,noff+1)
                ) (inp_mp1,latch_mp1,Map.empty,mp1,[],off1) (aigerLatches aiger)

      actionForGate :: Var -> Map Var Int -> Map Var (Int,Var,Bool) -> Map Var (PropL Int) -> Int -> (PropL Int,Int,[UnrollAction],Map Var Int,Map Var (Int,Var,Bool),Map Var (PropL Int))
      actionForGate gate inp_mp latch_mp mp off = case Map.lookup gate mp of
        Just f -> (f,off,[],inp_mp,latch_mp,mp)
        Nothing -> case getSymbol gate aiger of
          Input -> (Atom off,off+1,[PushInput gate],Map.insert gate off inp_mp,latch_mp,Map.insert gate (Atom off) mp)
          Latch -> let (latch_from,latch_pos) = getLatch gate aiger
                   in (Atom off,off+1,[PushLatch gate],inp_mp,Map.insert gate (off,latch_from,latch_pos) latch_mp,Map.insert gate (Atom off) mp)
          Gate -> let (gl,pl,gr,pr) = getGate gate aiger
                      (fl,off1,act_l,inp_mp1,latch_mp1,mp1) = actionForGate gl inp_mp latch_mp mp off
                      (fr,off2,act_r,inp_mp2,latch_mp2,mp2) = actionForGate gr inp_mp1 latch_mp1 mp1 off1
                      f = simplify (if gl==gr
                                    then (if not pl && not pr
                                          then Not fl
                                          else (if pl && pr
                                                then fl
                                                else Const False))
                                    else And (if pl then fl else Not fl) (if pr then fr else Not fr))
                  in case Map.lookup gate num_uses of
                    Nothing -> error $ "No usage information for gate "++show gate++" present "++show num_uses
                    Just 1 -> (f,off2,act_r++act_l,inp_mp2,latch_mp2,Map.insert gate (simplify $ And fl fr) mp2)
                    Just _ -> (Atom off2,off2+1,[PushFormula f]++act_r++act_l,inp_mp2,latch_mp2,Map.insert gate (Atom off2) mp2)

unrollingGetValue :: IArray arr Int => PropL Int -> arr Int Int -> PropL Var
unrollingGetValue f arr = flattenFormula $ fmap (\idx -> let lit = Lit $ arr!idx
                                                         in if litIsP lit
                                                            then Atom $ litVar lit
                                                            else Not $ Atom $ litVar lit) f

performUnrolling :: (Monad m,MArray marr Int m,IArray arr Int) => Proxy marr -> m Var -> (Formula -> m ()) -> Unrolling -> Map Var Lit -> m (arr Int Int)
performUnrolling prx nxt assert unroll latches = do
  arr <- createArray prx
  performUnrolling' nxt assert unroll latches 0 arr
  unsafeFreeze arr
  where
    createArray :: MArray marr Int m => Proxy marr -> m (marr Int Int)
    createArray _ = newArray_ (0,(unrollStackSize unroll)-1)

performUnrolling' :: (Monad m,MArray arr Int m) => m Var -> (Formula -> m ()) -> Unrolling -> Map Var Lit -> Int -> arr Int Int -> m ()
performUnrolling' nxt assert unroll latches off arr = case unrollmentActions unroll of
  [] -> return ()
  (act:acts) -> do
    case act of
      PushInput inp -> do
        v <- nxt
        writeArray arr off (litId $ lp v)
      PushLatch latch -> case Map.lookup latch latches of
        Just latch_lit -> writeArray arr off (litId latch_lit)
        Nothing -> error $ "Latch "++show latch++" not found"
      PushFormula f -> do
        rf <- mapM (\idx -> do
                       lit <- readArray arr idx
                       return $ if litIsP (Lit lit)
                                then Atom $ litVar (Lit lit)
                                else Not $ Atom $ litVar (Lit lit)
                   ) f
        (formula,lit) <- tseitin nxt (flattenFormula rf)
        assert formula
        writeArray arr off (litId lit)
    performUnrolling' nxt assert (unroll { unrollmentActions = acts }) latches (off+1) arr

getFormulaValue :: PropL Var -> [Bool] -> Bool
getFormulaValue (Const x) mdl = x
getFormulaValue (Atom v) mdl = List.genericIndex mdl v
getFormulaValue (Not f) mdl = not $ getFormulaValue f mdl
getFormulaValue (And x y) mdl = (getFormulaValue x mdl) && (getFormulaValue y mdl)
getFormulaValue (Or x y) mdl = (getFormulaValue x mdl) || (getFormulaValue y mdl)

runUnrolling :: IO Var -> (Formula -> IO ()) -> (Int -> IO ()) -> IO Bool -> IO [Bool] -> Unrolling -> Int -> PropL Var -> Map Var Var -> IO (Either [Map Var Bool] [(Map Var (PropL Var),Map Var Lit)])
runUnrolling nxt assert step chk model unroll n latch_f latches = do
  latch_cnf <- toCNF nxt latch_f
  assert latch_cnf
  trace <- doUnrolling nxt assert step unroll n (fmap lp latches)
  let formula = foldl1 Or [ outp | (_,outps,_,_) <- tail trace, outp <- Map.elems outps ]
      simpl_assertion = simplify formula
  cnf_assertion <- toCNF nxt simpl_assertion
  assert cnf_assertion
  res <- chk
  if res
    then (do
             mdl <- model
             return $ Left [ fmap (\inp -> getFormulaValue inp mdl) inps | (inps,_,_,_) <- trace ]
         )
    else return $ Right [ (outps,nlatch) | (_,outps,_,nlatch) <- trace ]

doUnrolling :: IO Var -> (Formula -> IO ()) -> (Int -> IO ()) -> Unrolling -> Int -> Map Var Lit -> IO [(Map Var (PropL Var),Map Var (PropL Var),Map Var Lit,Map Var Lit)]
doUnrolling nxt assert step unroll limit latches = doUnrolling' nxt assert step unroll limit 0 latches

doUnrolling' :: IO Var -> (Formula -> IO ()) -> (Int -> IO ()) -> Unrolling -> Int -> Int -> Map Var Lit -> IO [(Map Var (PropL Var),Map Var (PropL Var),Map Var Lit,Map Var Lit)]
doUnrolling' nxt assert step unroll limit cur latches
  | cur==limit = return []
  | otherwise = do
    step cur
    (inps,outps,olatch,nlatch) <- stepUnrolling nxt assert unroll latches
    els <- doUnrolling' nxt assert step unroll limit (cur+1) nlatch
    return $ (inps,outps,olatch,nlatch):els

stepUnrolling :: IO Var -> (Formula -> IO ()) -> Unrolling -> Map Var Lit -> IO (Map Var (PropL Var),Map Var (PropL Var),Map Var Lit,Map Var Lit)
stepUnrolling nxt assert unroll latches = do
  (arr::Array Int Int) <- performUnrolling (Proxy :: Proxy IOArray)
                          nxt
                          assert
                          unroll
                          latches
  let outps = fmap (\outp -> unrollingGetValue outp arr
                   ) (unrollOutputs unroll)
      olatch = fmap (\(off,_,_) -> Lit (arr!off)) (unrollLatches unroll)
      nlatch = fmap (\(off,_,pos) -> if pos
                                     then Lit (arr!off)
                                     else litNeg $ Lit (arr!off)
                    ) (unrollLatchesOut unroll)
      inps = fmap (\idx -> unrollingGetValue (Atom idx) arr) (unrollInputs unroll)
  return (inps,outps,olatch,nlatch)
