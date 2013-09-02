module Interpolation where

import Literal
import Formula
import ProofBuilder

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Foreign.C

import Debug.Trace

data VarLabel = Red | Blue | RedBlue deriving (Eq,Ord,Show)

type LabeledClause = Map Var (Bool,VarLabel)

getColorAndDelete :: Var -> LabeledClause -> (LabeledClause,VarLabel)
getColorAndDelete v cl = let (Just (_,col),ncl) = Map.updateLookupWithKey (\_ _ -> Nothing) v cl
                         in (ncl,col)

initialBInterpolant :: LabeledClause -> PropL Var
initialBInterpolant cl = let blue_cl = Map.filter (\(_,col) -> col==Blue) cl
                         in if Map.null blue_cl
                            then Const True
                            else Not $ foldl1 Or [ if pos then Atom v else Not (Atom v) | (v,(pos,_)) <- Map.toList blue_cl ]

initialAInterpolant :: LabeledClause -> PropL Var
initialAInterpolant cl = let red_cl = Map.filter (\(_,col) -> col==Red) cl
                         in if Map.null red_cl
                            then Const False
                            else foldl1 Or [ if pos then Atom v else Not (Atom v) | (v,(pos,_)) <- Map.toList red_cl ]

mergeClause :: LabeledClause -> LabeledClause -> LabeledClause
mergeClause = Map.unionWith (\(pos1,col1) (pos2,col2) -> if pos1==pos2
                                                         then (if col1==col2
                                                               then (pos1,col1)
                                                               else (pos1,RedBlue))
                                                         else error "Incompatible clauses")

interpolate :: LabeledClause -- ^ The left hand clause
            -> PropL Var -- ^ The left hand interpolant
            -> LabeledClause -- ^ The right hand clause
            -> PropL Var -- ^ The right hand interpolant
            -> Var -- ^ The variable eliminated
            -> (LabeledClause,PropL Var)
interpolate lcl lint rcl rint var
  = let (nlcl,lcolor) = getColorAndDelete var lcl
        (nrcl,rcolor) = getColorAndDelete var rcl
        res_int = case (lcolor,rcolor) of
          (Blue,Blue) -> Or lint rint
          (Red,Red) -> And lint rint
          _ -> And (Or (Atom var) lint) (Or (Not (Atom var)) rint)
        res_cl = mergeClause nlcl nrcl
    in {-trace ("Interpolating: "++show lcl++show [simplify lint]++" and "++show rcl++show [simplify rint]++" with var "++show var++" => "++show res_cl++show [simplify res_int])-} (res_cl,res_int)

class InterpolationSystem a where
  labelPartition :: a
                 -> Bool -- ^ Is the clause from the A partition?
                 -> (Var -> Bool) -- ^ Function to check if a variable is shared
                 -> [Lit] -- ^ The clause
                 -> LabeledClause

data InterpolationState a = InterpolationState { interpolationSystem :: a
                                               , sharedVars :: Var -> Bool
                                               , interpolationNodes :: Map CInt (LabeledClause,PropL Var)
                                               , nextInterpolationNode :: CInt
                                               , isAPartition :: Bool
                                               }

newInterpolationState :: a -> (Var -> Bool) -> InterpolationState a
newInterpolationState isys isShared = InterpolationState { interpolationSystem = isys
                                                         , sharedVars = isShared
                                                         , interpolationNodes = Map.empty
                                                         , nextInterpolationNode = 0
                                                         , isAPartition = True
                                                         }

setAPartition :: InterpolationState a -> InterpolationState a
setAPartition interp = interp { isAPartition = True }

setBPartition :: InterpolationState a -> InterpolationState a
setBPartition interp = interp { isAPartition = False }

interpolationRoot :: InterpolationSystem a => [Lit] -> InterpolationState a -> InterpolationState a
interpolationRoot cl interp = let labeledCl = labelPartition (interpolationSystem interp) (isAPartition interp) (sharedVars interp) cl
                                  interpolant = (if isAPartition interp
                                                 then initialAInterpolant
                                                 else initialBInterpolant) labeledCl
                              in interp { interpolationNodes = Map.insert (nextInterpolationNode interp) (labeledCl,interpolant) (interpolationNodes interp)
                                        , nextInterpolationNode = succ (nextInterpolationNode interp)
                                        }

interpolationChain :: [CInt] -> [Var] -> InterpolationState a -> InterpolationState a
interpolationChain [nd1,nd2] [v] interp = let Just (cl1,int1) = Map.lookup nd1 (interpolationNodes interp)
                                              Just (cl2,int2) = Map.lookup nd2 (interpolationNodes interp)
                                              intres = interpolate cl1 int1 cl2 int2 v
                                          in interp { interpolationNodes = Map.insert (nextInterpolationNode interp) intres (interpolationNodes interp)
                                                    , nextInterpolationNode = succ (nextInterpolationNode interp)
                                                    }

getInterpolant :: InterpolationState a -> PropL Var
getInterpolant interp = case Map.lookup (pred $ nextInterpolationNode interp) (interpolationNodes interp) of
  Just (cl,int) -> if Map.null cl
                   then int
                   else error "Incomplete interpolation"
  _ -> error "Interpolation hasn't completed yet."

simpleLabeling :: (VarLabel -> VarLabel) -> Bool -> (Var -> Bool) -> [Lit] -> LabeledClause
simpleLabeling f isAPart isShared
  = Map.fromList . fmap (\lit -> (litVar lit,(litIsP lit,if isShared (litVar lit)
                                                         then f RedBlue
                                                         else (if isAPart
                                                               then f Blue
                                                               else f Red))))

data McMillan = McMillan

instance InterpolationSystem McMillan where
  labelPartition _ = simpleLabeling (\c -> if c==Blue
                                            then Blue
                                            else Red)
data HKP = HKP

instance InterpolationSystem HKP where
  labelPartition _ = simpleLabeling id

interpolateProof :: InterpolationSystem a => a -> (Var -> Bool) -> ProofBuilder Bool -> PropL Var
interpolateProof isys isShared builder = let (cl,int) = interpolateProof' isys isShared (proofBuilderGet builder)
                                         in if Map.null cl
                                            then int
                                            else error "Unfinished interpolation."

interpolateProof' :: InterpolationSystem a => a -> (Var -> Bool) -> ProofNode Bool -> (LabeledClause,PropL Var)
interpolateProof' isys isShared (ProofRoot cl isA) = let labeledCl = labelPartition isys isA isShared (clauseLits cl)
                                                         interp = (if isA
                                                                   then initialAInterpolant
                                                                   else initialBInterpolant) labeledCl
                                                     in (labeledCl,interp)
interpolateProof' isys isShared (ProofChain (nd:nodes) vars)
  = foldl (\(cl,int) (nd',var') -> let (cl2,int2) = interpolateProof' isys isShared nd'
                                   in interpolate cl int cl2 int2 var'
          ) (interpolateProof' isys isShared nd) (zip nodes vars)

testInterpolation :: (LabeledClause,PropL Var)
testInterpolation = interpolate cl6 i6 cl4 i4 1
  where
    cl1 = Map.fromList [(1,(True,Blue)),(2,(False,Blue))]
    i1 = initialAInterpolant cl1
    cl2 = Map.fromList [(1,(False,Red)),(2,(True,RedBlue))]
    i2 = initialBInterpolant cl2
    cl3 = Map.fromList [(1,(True,Red))]
    i3 = initialBInterpolant cl3
    cl4 = Map.fromList [(1,(False,Blue))]
    i4 = initialAInterpolant cl4
    
    (cl5,i5) = interpolate cl3 i3 cl2 i2 1
    (cl6,i6) = interpolate cl5 i5 cl1 i1 2
