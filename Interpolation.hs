module Interpolation where

import Literal
import Formula
import ProofBuilder

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Foreign.C

data VarLabel = Red | Blue | RedBlue deriving (Eq,Ord,Show)

type LabeledClause a = [(VarLabel,a)]

getColorAndDelete :: (a -> Bool) -> LabeledClause a -> (LabeledClause a,VarLabel)
getColorAndDelete f [] = error "Error while interpolating: Eliminated variable not in clause"
getColorAndDelete f ((lbl,v):cls)
  | f v = (cls,lbl)
  | otherwise = let (rest,res) = getColorAndDelete f cls
                in ((lbl,v):rest,res)

initialBInterpolant :: Literal a => LabeledClause a -> PropL Var
initialBInterpolant cl = case filter (\(lbl,_) -> lbl==Blue) cl of
  [] -> Const True
  xs -> Not $ foldl1 Or $ fmap (\(_,x) -> if litIsP x
                                          then Atom (litVar x)
                                          else Not (Atom (litVar x))
                               ) xs

initialAInterpolant :: Literal a => LabeledClause a -> PropL Var
initialAInterpolant cl = case filter (\(lbl,_) -> lbl==Red) cl of
  [] -> Const False
  xs -> foldl1 Or $ fmap (\(_,x) -> if litIsP x
                                    then Atom (litVar x)
                                    else Not (Atom (litVar x))
                         ) xs

interpolate :: Literal a
               => LabeledClause a -- ^ The left hand clause
               -> PropL Var -- ^ The left hand interpolant
               -> LabeledClause a -- ^ The right hand clause
               -> PropL Var -- ^ The right hand interpolant
               -> Var -- ^ The variable eliminated
               -> (LabeledClause a,PropL Var)
interpolate lcl lint rcl rint var
  = let (nlcl,lcolor) = getColorAndDelete (\v -> litVar v == var) lcl
        (nrcl,rcolor) = getColorAndDelete (\v -> litVar v == var) rcl
    in (nlcl++nrcl,case (lcolor,rcolor) of
           (Blue,Blue) -> Or lint rint
           (Red,Red) -> And lint rint
           _ -> And (Or (Atom var) lint) (Or (Not (Atom var)) rint))

class InterpolationSystem a where
  labelPartition :: a
                 -> Bool -- ^ Is the clause from the A partition?
                 -> (Var -> Bool) -- ^ Function to check if a variable is shared
                 -> [Lit] -- ^ The clause
                 -> LabeledClause Lit

data InterpolationState a = InterpolationState { interpolationSystem :: a
                                               , sharedVars :: Var -> Bool
                                               , interpolationNodes :: Map CInt (LabeledClause Lit,PropL Var)
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
  Just ([],int) -> int
  _ -> error "Interpolation hasn't completed yet."

simpleLabeling :: (VarLabel -> VarLabel) -> Bool -> (Var -> Bool) -> [Lit] -> LabeledClause Lit
simpleLabeling f isAPart isShared = fmap (\lit -> if isShared (litVar lit)
                                                  then (f RedBlue,lit)
                                                  else (if isAPart
                                                        then (f Blue,lit)
                                                        else (f Red,lit)))

data McMillan = McMillan

instance InterpolationSystem McMillan where
  labelPartition _ = simpleLabeling (\c -> if c==Blue
                                            then Blue
                                            else Red)
data HKP = HKP

instance InterpolationSystem HKP where
  labelPartition _ = simpleLabeling id

interpolateProof :: InterpolationSystem a => a -> (Var -> Bool) -> ProofBuilder Bool -> PropL Var
interpolateProof isys isShared builder = case interpolateProof' isys isShared (proofBuilderGet builder) of
  ([],int) -> int
  _ -> error "Unfinished interpolation."

interpolateProof' :: InterpolationSystem a => a -> (Var -> Bool) -> ProofNode Bool -> (LabeledClause Lit,PropL Var)
interpolateProof' isys isShared (ProofRoot cl isA) = let labeledCl = labelPartition isys isA isShared (clauseLits cl)
                                                         interp = (if isA
                                                                   then initialAInterpolant
                                                                   else initialBInterpolant) labeledCl
                                                     in (labeledCl,interp)
interpolateProof' isys isShared (ProofChain (nd:nodes) vars)
  = foldl (\(cl,int) (nd',var') -> let (cl2,int2) = interpolateProof' isys isShared nd'
                                   in interpolate cl int cl2 int2 var'
          ) (interpolateProof' isys isShared nd) (zip nodes vars)

testInterpolation :: (LabeledClause Lit,PropL Var)
testInterpolation = interpolate cl6 i6 cl4 i4 1
  where
    cl1 = [(Blue,lp 1),(Blue,ln 2)]
    i1 = initialAInterpolant cl1
    cl2 = [(Red,ln 1),(RedBlue,lp 2)]
    i2 = initialBInterpolant cl2
    cl3 = [(Red,lp 1)]
    i3 = initialBInterpolant cl3
    cl4 = [(Blue,ln 1)]
    i4 = initialAInterpolant cl4
    
    (cl5,i5) = interpolate cl3 i3 cl2 i2 1
    (cl6,i6) = interpolate cl5 i5 cl1 i1 2
