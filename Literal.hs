module Literal where

import Foreign.C
import Data.Bits
import Foreign.Storable

newtype Var = Var CInt deriving (Eq,Ord,Storable)
newtype Lit = Lit CInt deriving (Eq,Ord,Storable)

instance Show Lit where
  show l = if litSign l
           then (show $ litVar l)
           else ("!"++show (litVar l))

instance Show Var where
  show (Var x) = "v"++show x

lit :: Var -> Bool -> Lit
lit (Var var) sgn = Lit ((var+var)+(if sgn then 1 else 0))

lp :: Var -> Lit
lp (Var var) = Lit (var+var+1)

ln :: Var -> Lit
ln (Var var) = Lit (var+var)

litVar :: Lit -> Var
litVar (Lit x) = Var (x `shiftR` 1)

litSign :: Lit -> Bool
litSign (Lit x) = (x .&. 1) /= 0
