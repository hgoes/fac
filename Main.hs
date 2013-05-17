module Main where

import Control.Monad
import Minisat
import Data.IORef
import Data.Map as Map
import Foreign.C

data ProofNode = ProofRoot [Lit]
               | ProofChain [ProofNode] [Var]
               deriving Show

data ProofBuilder = ProofBuilder { proofNodes :: Map CInt ProofNode
                                 , nextNode :: CInt }

proofBuilder :: ProofBuilder
proofBuilder = ProofBuilder Map.empty 0

proofBuilderRoot :: [Lit] -> ProofBuilder -> ProofBuilder
proofBuilderRoot lits builder = builder { proofNodes = Map.insert (nextNode builder) (ProofRoot lits) (proofNodes builder)
                                        , nextNode = succ (nextNode builder)
                                        }

proofBuilderChain :: [CInt] -> [Var] -> ProofBuilder -> ProofBuilder
proofBuilderChain cls vars builder = let cls' = fmap ((proofNodes builder)!) cls
                                     in builder { proofNodes = Map.insert (nextNode builder) (ProofChain cls' vars) (proofNodes builder)
                                                , nextNode = succ (nextNode builder)
                                                }

proofBuilderDelete :: CInt -> ProofBuilder -> ProofBuilder
proofBuilderDelete cl builder = builder { proofNodes = Map.delete cl (proofNodes builder) }

proofBuilderGet :: ProofBuilder -> ProofNode
proofBuilderGet builder = (proofNodes builder)!(pred $ nextNode builder)

main = do
  solv <- solverNew
  {-
 1  2 -3 0
-1 -2  3 0
 2  3 -4 0
-2 -3  4 0
 1  3  4 0
-1 -3 -4 0
-1  2  4 0
 1 -2 -4 0
-}
  builder <- newIORef proofBuilder
  solverAddProofLog solv
    (modifyIORef builder . proofBuilderRoot)
    (\cls vars -> modifyIORef builder $ proofBuilderChain cls vars)
    (modifyIORef builder . proofBuilderDelete)
    (putStrLn "Done!")
  vars@[v1,v2,v3,v4] <- replicateM 4 (solverNewVar solv)
  print vars
  mapM_ (\cl -> do
            --solverOk solv >>= print
            --print cl
            solverAddClause solv cl)
    [[lp v1,lp v2,ln v3]
    ,[ln v1,ln v2,lp v3]
    ,[lp v2,lp v3,ln v4]
    ,[ln v2,ln v3,lp v4]
    ,[lp v1,lp v3,lp v4]
    ,[ln v1,ln v3,ln v4]
    ,[ln v1,lp v2,lp v4]
    ,[lp v1,ln v2,ln v4]]
  solverSolve solv >>= print
  solverGetModel solv >>= print
  readIORef builder >>= print . proofBuilderGet