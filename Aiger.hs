module Aiger where

import Literal

readLit :: String -> Lit
readLit = Lit . read

data Aiger lit = Aiger { aigerMaxVar :: lit
                       , aigerInputs :: [lit]
                       , aigerLatches :: [(lit,lit)]
                       , aigerOutputs :: [lit]
                       , aigerGates :: [(lit,lit,lit)]
                       , aigerSymbols :: [(Symbol,Integer,String)]
                       , aigerComments :: [String]
                       } deriving (Show)

data Symbol = Input
            | Latch
            | Output
            deriving (Show,Eq,Ord)

readAiger :: (String -> lit) -> String -> Aiger lit
readAiger parse str = case lines str of
  header:rest -> case words header of
    ["aag",max_var,n_inp,n_latch,n_outp,n_and]
      -> let (inp_lines,rest1) = splitAt (read n_inp) rest
             (latch_lines,rest2) = splitAt (read n_latch) rest1
             (outp_lines,rest3) = splitAt (read n_outp) rest2
             (and_lines,rest4) = splitAt (read n_and) rest3
             (syms,comms) = parseSymbols rest3
         in Aiger { aigerMaxVar = parse max_var
                  , aigerInputs = [ parse ln | ln <- inp_lines ]
                  , aigerLatches = [ (parse l1,parse l2) | [l1,l2] <- fmap words latch_lines ]
                  , aigerOutputs = [ parse ln | ln <- outp_lines ]
                  , aigerGates = [ (parse l1,parse l2,parse l3) | [l1,l2,l3] <- fmap words and_lines ]
                  , aigerSymbols = syms
                  , aigerComments = comms
                  }
    ("aig":_) -> error "Binary aiger format not yet supported."
    _ -> error "Wrong header of aiger file."
  where
    parseSymbols :: [String] -> ([(Symbol,Integer,String)],[String])
    parseSymbols [] = ([],[])
    parseSymbols (x:xs) = case x of
      "c" -> ([],xs)
      sym:rest -> let (num,_:name) = span (/=' ') rest
                      sym' = case sym of
                        'i' -> Input
                        'l' -> Latch
                        'o' -> Output
                      (syms,comms) = parseSymbols xs
                  in ((sym',read num,name):syms,comms)