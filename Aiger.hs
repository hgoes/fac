module Aiger where

data AigerLit = AigerLit { aigerLitId :: Integer
                         , aigerLitNegated :: Bool }

instance Show AigerLit where
  show lit = (if aigerLitNegated lit
              then "!"
              else "")++show (aigerLitId lit)

readLit :: String -> AigerLit
readLit = toLit . read

toLit :: Integer -> AigerLit
toLit n = let (i,r) = n `divMod` 2
          in AigerLit i (r==1)

data Aiger = Aiger { aigerMaxVar :: Integer
                   , aigerInputs :: [AigerLit]
                   , aigerLatches :: [(AigerLit,AigerLit)]
                   , aigerOutputs :: [AigerLit]
                   , aigerGates :: [(AigerLit,AigerLit,AigerLit)]
                   } deriving (Show)

readAiger :: String -> Aiger
readAiger str = case lines str of
  header:rest -> case words header of
    ["aag",max_var,n_inp,n_latch,n_outp,n_and]
      -> let (inp_lines,rest1) = splitAt (read n_inp) rest
             (latch_lines,rest2) = splitAt (read n_latch) rest1
             (outp_lines,rest3) = splitAt (read n_outp) rest2
             (and_lines,rest4) = splitAt (read n_and) rest3
         in Aiger { aigerMaxVar = read max_var
                  , aigerInputs = [ readLit ln | ln <- inp_lines ]
                  , aigerLatches = [ (readLit l1,readLit l2) | [l1,l2] <- fmap words latch_lines ]
                  , aigerOutputs = [ readLit ln | ln <- outp_lines ]
                  , aigerGates = [ (readLit l1,readLit l2,readLit l3) | [l1,l2,l3] <- fmap words and_lines ]
                  }
    ("aig":_) -> error "Binary aiger format not yet supported."
    _ -> error "Wrong header of aiger file."