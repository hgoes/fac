module Simulator where

import Aiger
import Literal

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable

simulateAiger :: Literal lit => Aiger lit -> [Map Var Bool] -> [Map Var Bool]
simulateAiger aiger = snd . mapAccumL (stepAiger aiger) (Map.fromList [ (litVar latch_to,False) | (latch_to,_) <- aigerLatches aiger ])

-- | Run one step in the aiger model.
--   Returns new latches and outputs.
stepAiger :: Literal lit
             => Aiger lit
             -> Map Var Bool -- ^ Latches
             -> Map Var Bool -- ^ Inputs
             -> (Map Var Bool,Map Var Bool)
stepAiger aiger latch inp
  = (nlatch,outps)
  where
    (outps,mp1) = foldl (\(cout,cmp) outp 
                         -> let (v,nmp) = getGateVal cmp outp
                            in (Map.insert (litVar outp) v cout,nmp)
                        ) (Map.empty,Map.union inp latch) (aigerOutputs aiger)
    (nlatch,mp2) = foldl (\(clatch,cmp) (latch_to,latch_from)
                          -> let (v,nmp) = getGateVal cmp latch_from
                             in (Map.insert (litVar latch_to) v clatch,nmp)
                         ) (Map.empty,mp1) (aigerLatches aiger)
    getGateVal mp gate = case Map.lookup (litVar gate) mp of
      Just v -> (if litIsP gate
                 then v
                 else not v,mp)
      Nothing -> let (g1,g2) = getGate (litVar gate) aiger
                     (v1,mp1) = getGateVal mp g1
                     (v2,mp2) = getGateVal mp1 g2
                     res = if litIsP gate
                           then v1 && v2
                           else not (v1 && v2)
                 in (res,Map.insert (litVar gate) res mp2)