module Simulator where

import Aiger
import Literal

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable

simulateAiger :: AigerC aiger => aiger -> [Map Var Bool] -> [[Bool]]
simulateAiger aiger = snd . mapAccumL (stepAiger aiger) (Map.fromList [ (latch_to,False) | (latch_to,_,_) <- aigerLatches aiger ])

-- | Run one step in the aiger model.
--   Returns new latches and outputs.
stepAiger :: AigerC aiger
             => aiger
             -> Map Var Bool -- ^ Latches
             -> Map Var Bool -- ^ Inputs
             -> (Map Var Bool,[Bool])
stepAiger aiger latch inp
  = (nlatch,outps)
  where
    (mp1,outps) = mapAccumL (\cmp outp -> let (v,nmp) = getGateVal cmp (litVar outp) (litIsP outp)
                                          in (nmp,v)) (Map.union inp latch) (aigerOutputs aiger)
    (nlatch,mp2) = foldl (\(clatch,cmp) (latch_to,latch_pos,latch_from)
                          -> let (v,nmp) = getGateVal cmp latch_from latch_pos
                             in (Map.insert latch_to v clatch,nmp)
                         ) (Map.empty,mp1) (aigerLatches aiger)
    getGateVal mp gate pos = case Map.lookup gate mp of
      Just v -> (if pos
                 then v
                 else not v,mp)
      Nothing -> let (g1,p1,g2,p2) = getGate gate aiger
                     (v1,mp1) = getGateVal mp g1 p1
                     (v2,mp2) = getGateVal mp1 g2 p2
                     res = if pos
                           then v1 && v2
                           else not (v1 && v2)
                 in (res,Map.insert gate (v1 && v2) mp2)
