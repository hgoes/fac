module Interpolation where

import Literal
import Formula

data VarLabel = Red | Blue | RedBlue deriving (Eq,Ord,Show)

type LabeledClause a = [(VarLabel,a)]

getColorAndDelete :: (a -> Bool) -> LabeledClause a -> (LabeledClause a,VarLabel)
getColorAndDelete f [] = error "Error while interpolating: Eliminated variable not in clause"
getColorAndDelete f ((lbl,v):cls)
  | f v = (cls,lbl)
  | otherwise = let (rest,res) = getColorAndDelete f cls
                in ((lbl,v):rest,res)

initialRedInterpolant :: Literal a => LabeledClause a -> PropL Var
initialRedInterpolant cl = case filter (\(lbl,_) -> lbl==Blue) cl of
  [] -> Const True
  xs -> Not $ foldl1 Or $ fmap (\(_,x) -> if litIsP x
                                          then Atom (litVar x)
                                          else Not (Atom (litVar x))
                               ) xs

initialBlueInterpolant :: Literal a => LabeledClause a -> PropL Var
initialBlueInterpolant cl = case filter (\(lbl,_) -> lbl==Red) cl of
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

testInterpolation :: (LabeledClause Lit,PropL Var)
testInterpolation = interpolate cl6 i6 cl4 i4 1
  where
    cl1 = [(Blue,lp 1),(Blue,ln 2)]
    i1 = initialBlueInterpolant cl1
    cl2 = [(Red,ln 1),(RedBlue,lp 2)]
    i2 = initialRedInterpolant cl2
    cl3 = [(Red,lp 1)]
    i3 = initialRedInterpolant cl3
    cl4 = [(Blue,ln 1)]
    i4 = initialBlueInterpolant cl4
    
    (cl5,i5) = interpolate cl3 i3 cl2 i2 1
    (cl6,i6) = interpolate cl5 i5 cl1 i1 2
