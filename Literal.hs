module Literal where

import Data.Bits
import Foreign.Storable

newtype Var = Var { varId :: Int } deriving (Eq,Ord,Storable,Enum,Num)
newtype Lit = Lit { litId :: Int } deriving (Eq,Ord,Storable,Enum,Num)

instance Show Lit where
  show l = if litSign l
           then (show $ litVar l)
           else ("!"++show (litVar l))

instance Show Var where
  show (Var x) = "v"++show x

lit :: Var -> Bool -> Lit
lit (Var var) sgn = Lit ((var+var)+(if sgn then 1 else 0))

lp :: Var -> Lit
lp (Var var) = Lit (var+var)

ln :: Var -> Lit
ln (Var var) = Lit (var+var+1)

litVar :: Lit -> Var
litVar (Lit x) = Var (x `shiftR` 1)

litSign :: Lit -> Bool
litSign (Lit x) = (x .&. 1) /= 0

litNeg :: Lit -> Lit
litNeg (Lit x) = Lit (x `xor` 1)