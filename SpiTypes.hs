{-# LANGUAGE RecordWildCards, TypeSynonymInstances, FlexibleInstances #-}
module SpiTypes where

import Control.Monad
import Control.Monad.State.Strict
import Control.Concurrent.STM.TMVar
import Control.Concurrent.MVar
--Pi
data Pi = Name String
        | Pair Pi Pi
        | Zero
        | Succ Pi
        | Var String 
        | Encryption Pi Pi deriving ( Eq)

instance Show Pi where
    show (Name str) = str
    show (Pair x (Pair y (Pair z w))) = "{" ++ (show x) ++ ", " ++ (show y) ++ ", " ++ (show z) ++ ", " ++ (show w) ++ "}"
    show (Pair x (Pair y z)) = "{" ++ (show x) ++ ", " ++ (show y) ++ ", " ++ (show z) ++ "}"
    show (Pair x y) = "{" ++ (show x) ++ ", " ++ (show y) ++ "}"
    show Zero       = "0"
    show (Succ x)   = "Succ(" ++ (show x) ++ ")"
    show (Var x)    = "Var " ++ x
    show (Encryption mess key) = "{" ++ (show mess) ++ "}^" ++ (show key)    
    
--Pi types
data PiType = TName   
            | TPair PiType PiType
            | TSucc
            | TVar
            | TZero 
            | TEncryption deriving (Show, Eq)
                                   
 
--PiProcess       
data PiProcess = Output Pi Pi PiProcess
               | Input Pi (Pi) PiProcess --Input Pi (Var String) PiProcess
               | Composition PiProcess PiProcess
               | Restriction (Pi) PiProcess --Restriction (Name String) PiProcess
               | Replication PiProcess
               | Match Pi Pi PiProcess
               | Nil
               | Let (Pi,Pi) Pi PiProcess
               | Case Pi Pi PiProcess Pi PiProcess 
               | Chain [PiProcess]
               | EmptyChain
               | Value Pi
               | OrderedOutput Int String String Pi PiProcess
               | CaseDecrypt Pi Pi Pi PiProcess
               | Stuck deriving (Eq)    

instance Show PiProcess where
        show (Output chan mess nextproc) = (show chan) ++ "<\"" ++ (show mess) ++ "\"> . " ++ (show nextproc)
        show (Input chan mess nextproc)  = (show chan) ++ "(" ++ (show mess) ++ ") . " ++ (show nextproc)
        show (Composition p1 (Composition p2 (Composition p3 (Composition p4 p5))))         = "\n " ++ (show p1) ++ " |\n " ++ (show p2) ++ " |\n " ++ (show p3) ++ " |\n " ++ (show p4)  ++ " |\n " ++ (show p5)
        show (Composition p1 (Composition p2 (Composition p3 p4)))         = "\n " ++ (show p1) ++ " |\n " ++ (show p2) ++ " |\n " ++ (show p3) ++ " |\n " ++ (show p4)
        show (Composition p1 (Composition p2 p3))         = "\n " ++ (show p1) ++ " |\n " ++ (show p2) ++ " |\n " ++ (show p3) ++ " "
        show (Composition p1 p2)         = "\n " ++ (show p1) ++ " |\n " ++ (show p2)
        show (Restriction pi piproc)     = "(v" ++ (show pi) ++ ")" ++ (show piproc)
        show (Replication piproc)        = "!" ++ (show piproc)
        show (Match pi1 pi2 piproc)      = "[" ++ (show pi1) ++ " is " ++ (show pi2) ++ "] " ++ (show piproc)    --[M is N] P
        show Nil                         = "Nil "
        show (Let (pi1,pi2) pi3 piproc)  = "let (" ++ (show pi1) ++ ", " ++ (show pi2) ++ ") = " ++ (show pi3) ++ " in " ++ (show piproc) --let (x; y) = M in P 
        show (Case x y yproc z zpiproc)         = "case " ++ (show x) ++ " of " ++ (show y) ++ " : " ++ (show yproc) ++ " " ++ (show z) ++ " : " ++ (show z) --case M of 0 : P suc(x) : Q 
        show (Chain procs)               = join (map show procs)
        show EmptyChain                  = "EmptyChain"
        show (Value pi)                  = "Value " ++ (show pi)
        show (OrderedOutput i f t mess nproc) = "(OrderedOutput " ++ (show i) ++ " " ++ f ++ "-->" ++ t ++ " " ++ (show mess) ++ ") . " ++ (show nproc)
        show (CaseDecrypt enc var key nproc)  = "case " ++ (show enc) ++ " of " ++ "{" ++ (show var) ++ "}^" ++ (show nproc) ++ " in " ++ (show nproc) --case L of fxgN in P
        show Stuck                           = "STUCK"
--PiProcess types
data PiProcessType = TOutput PiProcessType
                   | TInput PiProcessType
                   | TComposition PiProcessType PiProcessType
                   | TRestriction PiProcessType
                   | TReplication PiProcessType
                   | TMatch PiProcessType
                   | TNil
                   | TLet PiProcessType
                   | TCase 
                   | TValue
                   | TCaseDecryption PiProcessType
                   | TChain [PiProcessType] deriving (Show, Eq)   

data GammaMembers = VarBind (Pi, Pi)
                  | Restricted Pi deriving (Show, Eq)
type Gamma = [GammaMembers]
type GlobalChannels = (TMVar [(Pi,MVar (Pi, Int))])
emptyPiMVarPairList = [] :: [(Pi, MVar (Pi,Int))]
data MyState = MyState {
                            gamma :: Gamma,
                            globalChans :: GlobalChannels,
                            usedIDs :: [Int],
                            globID  :: (MVar Int)
                          } deriving (Eq)
type MyStateTMonad a = StateT MyState IO a 

--instance Show (MyStateT PiProcess) where
 --  show (StateT x) = "special: "
 --  show x = "feijf"   
--instance NFData (MyStateT PiProcess)                   