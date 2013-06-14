module Aiger where

import Literal
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

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
            | Unknown
            deriving (Show,Eq,Ord)

readAiger :: Read lit => String -> Aiger lit
readAiger str = case lines str of
  header:rest -> case words header of
    ("aag":max_var:n_inp:n_latch:n_outp:n_and:extras)
      -> let (inp_lines,rest1) = splitAt (read n_inp) rest
             (latch_lines,rest2) = splitAt (read n_latch) rest1
             (outp_lines,rest3) = splitAt (read n_outp) rest2
             (and_lines,rest4) = splitAt (read n_and) rest3
             rest5 = drop (sum $ fmap read extras) rest4
             (syms,comms) = parseSymbols rest5
         in Aiger { aigerMaxVar = read max_var
                  , aigerInputs = [ read ln | ln <- inp_lines ]
                  , aigerLatches = [ (read l1,read l2) | [l1,l2] <- fmap words latch_lines ]
                  , aigerOutputs = [ read ln | ln <- outp_lines ]
                  , aigerGates = [ (read l1,read l2,read l3) | [l1,l2,l3] <- fmap words and_lines ]
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
                        _ -> Unknown
                      (syms,comms) = parseSymbols xs
                  in ((sym',read num,name):syms,comms)

countUses :: (Literal lit) => Aiger lit -> Map Var Int
countUses aiger = let inc key = Map.alter (\entr -> case entr of
                                              Nothing -> Just 1
                                              Just n -> Just (n+1)
                                          ) key
                      mp1 = foldl (\cmp (_,latch_from) -> inc (litVar latch_from) cmp) Map.empty (aigerLatches aiger)
                      mp2 = foldl (\cmp outp -> inc (litVar outp) cmp) mp1 (aigerOutputs aiger)
                      mp3 = foldl (\cmp (_,in1,in2) -> if litVar in1==litVar in2 
                                                       then inc (litVar in1) cmp else inc (litVar in1) (inc (litVar in2) cmp)) mp2 (aigerGates aiger)
                  in mp3

isInput :: Literal lit => Var -> Aiger lit -> Bool
isInput var aiger = case List.find (\lit -> litVar lit == var) (aigerInputs aiger) of
  Nothing -> False
  Just _ -> True

getGate :: Literal lit => Var -> Aiger lit -> (lit,lit)
getGate gate aiger = case List.find (\(gt,_,_) -> litVar gt == gate) (aigerGates aiger) of
  Just (_,in1,in2) -> (in1,in2)