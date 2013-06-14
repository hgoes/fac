module Literal where

import Data.Bits
import Foreign.Storable
import Text.Read

newtype Var = Var { varId :: Int } deriving (Eq,Ord,Storable,Enum,Num,Real,Integral)
newtype Lit = Lit { litId :: Int } deriving (Eq,Ord,Storable,Enum,Num,Real,Integral)

instance Read Lit where
  readsPrec p str = [ (Lit res,rest) | (res,rest) <- readsPrec p str ]
  readPrec = fmap Lit readPrec

instance Show Lit where
  show l = if litSign l
           then (show $ litVar l)
           else ("!"++show (litVar l))

instance Show Var where
  show (Var x) = "v"++show x

class Literal l where
  lit :: Var -> Bool -> l
  lp :: Var -> l
  lp v = lit v True
  ln :: Var -> l
  ln v = lit v False
  litVar :: l -> Var
  litSign :: l -> Bool
  litNeg :: l -> l

instance Literal Lit where
  lit (Var var) sgn = Lit ((var+var)+(if sgn then 1 else 0))
  lp (Var var) = Lit (var+var)
  ln (Var var) = Lit (var+var+1)
  litVar (Lit x) = Var (x `shiftR` 1)
  litSign (Lit x) = (x .&. 1) /= 0
  litNeg (Lit x) = Lit (x `xor` 1)