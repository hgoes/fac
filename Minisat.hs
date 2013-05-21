module Minisat
       (Var()
       ,Lit(),lit,lp,ln,litVar,litSign
       ,Solver()
       ,solverNew
       ,solverNewVar
       ,solverAddClause
       ,solverOk
       ,solverSolve
       ,solverGetModel
       ,solverAddProofLog
       ) where

import Foreign.Ptr
import Foreign.C
import Foreign.Marshal
import Foreign.Storable
import Literal

newtype Solver = Solver (Ptr Solver)

solverAddClause :: Solver -> [Lit] -> IO ()
solverAddClause s cl = do
  let sz = length cl
  arr <- mallocArray sz
  pokeArray arr cl
  solverAddClause_ s arr (fromIntegral sz)

solverGetModel :: Solver -> IO [Bool]
solverGetModel solver
  = alloca (\arr -> do
               sz <- solverGetModel' solver arr
               arr' <- peek arr
               lst <- peekArray (fromIntegral sz) arr'
               return $ fmap (\i -> case i of
                                 1 -> True
                                 -1 -> False) lst
           )

solverAddProofLog :: Solver -> ([Lit] -> IO ()) -> ([CInt] -> [Var] -> IO ()) -> (CInt -> IO ()) -> IO () -> IO ()
solverAddProofLog solver root chain deleted done = do
  root' <- mkRootFun (\arr sz -> do
                         lst <- peekArray (fromIntegral sz) arr
                         root (fmap Lit lst))
  chain' <- mkChainFun (\carr csz varr vsz -> do
                           clst <- peekArray (fromIntegral csz) carr
                           vlst <- peekArray (fromIntegral vsz) varr
                           chain clst (fmap Var vlst))
  deleted' <- mkDeletedFun deleted
  done' <- mkDoneFun done
  solverAddProofLog' solver root' chain' deleted' done'
                         

foreign import capi "CInterface.h solver_new"
  solverNew :: IO Solver

foreign import capi "CInterface.h solver_add_proof_log"
  solverAddProofLog' :: Solver
                        -> FunPtr (Ptr CInt -> CInt -> IO ())
                        -> FunPtr (Ptr CInt -> CInt -> Ptr CInt -> CInt -> IO ())
                        -> FunPtr (CInt -> IO ())
                        -> FunPtr (IO ())
                        -> IO ()

foreign import ccall "wrapper"
  mkRootFun :: (Ptr CInt -> CInt -> IO ()) -> IO (FunPtr (Ptr CInt -> CInt -> IO ()))

foreign import ccall "wrapper"
  mkChainFun :: (Ptr CInt -> CInt -> Ptr CInt -> CInt -> IO ()) -> IO (FunPtr (Ptr CInt -> CInt -> Ptr CInt -> CInt -> IO ()))

foreign import ccall "wrapper"
  mkDeletedFun :: (CInt -> IO ()) -> IO (FunPtr (CInt -> IO ()))

foreign import ccall "wrapper"
  mkDoneFun :: IO () -> IO (FunPtr (IO ()))

foreign import capi "CInterface.h solver_new_var"
  solverNewVar :: Solver -> IO Var

foreign import capi "CInterface.h solver_add_clause"
  solverAddClause_ :: Solver -> Ptr Lit -> CInt -> IO ()

foreign import capi "CInterface.h solver_ok"
  solverOk :: Solver -> IO Bool

foreign import capi "CInterface.h solver_solve"
  solverSolve :: Solver -> IO Bool

foreign import capi "CInterface.h solver_solve_with"
  solverSolveWith :: Solver -> Ptr CInt -> CInt -> IO ()

foreign import capi "CInterface.h solver_get_model"
  solverGetModel' :: Solver -> Ptr (Ptr CInt) -> IO CInt