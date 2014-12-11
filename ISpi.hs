--pi calculus language
module ISpi where


import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import System.IO.Unsafe
--Pi
data Pi = Name String
	| Pair Pi Pi
	| Zero
	| Succ Pi
        | Var String deriving (Show, Eq)        
--Pi types
data PiType = TName   
            | TPair PiType PiType
            | TSucc
            | TVar
            | TZero deriving (Show, Eq)

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
               | Stuck deriving (Show, Eq)
badpieProc = Output Zero Zero Nil               
example1PiProcess = Output (Name "channel") (Name "message") Nil
example2PiProcess = Input (Name "channel") (Name "message") Nil
example3CompositionPiProcess = Composition example1PiProcess example2PiProcess
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
                   | TChain [PiProcessType] deriving (Eq, Show)
        
data Protocol = Proto PiProcess
              | Protocol `Then` Protocol
        
        



typeCheckPi :: Pi -> Either String PiType
typeCheckPi (Name str) = Right TName
typeCheckPi (Pair a b) = case typeCheckPi a of
                                Left str -> Left ("First of Pair type fail: " ++ str) 
                                Right fstT -> case typeCheckPi b of
                                                Left str -> Left ("Second member of Pair type fail: " ++ str)
                                                Right sndT ->  Right (TPair fstT sndT)                                
typeCheckPi Zero = Right TZero
typeCheckPi x@(Succ t) = case typeCheckPi t of
                              Left str -> Left (str) --no extra error text here to prevent recursive error message. 
                              Right TZero -> Right TSucc
                              Right TSucc -> Right TSucc
                              Right TVar  -> Right TSucc -- variables are okay, but may cause runtime error
                              Right _ -> Left ("Succ of non-numberic type: " ++ (show x))
typeCheckPi (Var _) = Right TVar                              
typeCheckPi x = Left ("Type failure: " ++ (show x))


testPiGood = Pair (Succ (Succ (Succ Zero))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
testPi1Good = Pair (Succ (Succ (Succ (Var "varhere1")))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
testPi2Bad = Pair (Succ (Succ (Succ (Name "name")))) (Pair (Name "namehere") (Pair Zero (Name "varhere")))

typeCheckPiProcess :: PiProcess -> Either String PiProcessType
typeCheckPiProcess (Input pi1 pi2 piProPrime) = case typeCheckPi pi1 of
      Left err   -> Left ("term 'Input' type fail on first pi argument: " ++ err)
      Right tpi1 -> if acceptablePi TName tpi1 then
         case typeCheckPi pi2 of
            Left err   -> Left ("term 'Input' type fail on second pi argument: " ++ err)
            Right tpi2 -> case typeCheckPiProcess piProPrime of
               Left err     -> Left ("terpm 'Input' type fail on process subterm: " ++ err)
               Right primeT -> Right (TInput primeT)
      else Left ("Input on non-channel. Expected TName for channel. Actual type: " ++ (show tpi1))
typeCheckPiProcess (Output pi1 pi2 piProPrime) = case typeCheckPi pi1 of
      Left err   -> Left ("term 'Output' type fail on first pi argument: " ++ err)
      Right tpi1 -> if acceptablePi TName tpi1 then
         case typeCheckPi pi2 of
            Left err   -> Left ("term 'Output' type fail on second pi argument: " ++ err)
            Right tpi2 -> case typeCheckPiProcess piProPrime of
               Left err     -> Left ("terpm 'Output' type fail on process subterm: " ++ err)
               Right primeT -> Right (TOutput primeT)
         else Left ("Output on non-channel. Expected TName for channel. Actual type: " ++ (show tpi1))
typeCheckPiProcess (Composition proc1 proc2) = case typeCheckPiProcess proc1 of
      Left err     -> Left ("Type error in term 'Composition', first process: " ++ err)
      Right proc1T -> case typeCheckPiProcess proc2 of
         Left err     -> Left ("Type error in term 'Composition', second process: " ++ err)
         Right proc2T -> Right (TComposition proc1T proc2T)
typeCheckPiProcess (Restriction pi1 proc) = case typeCheckPi pi1 of
      Left err   -> Left ("Type error in term 'Restriction' Pi term: " ++ err)
      Right pi1T -> case typeCheckPiProcess proc of
         Left err   -> Left ("Type error in term 'Restriction' Process term: " ++ err)
         Right procT -> Right (TRestriction procT)
typeCheckPiProcess (Replication proc) = case typeCheckPiProcess proc of
      Left err -> Left ("Type error in term 'Replication': " ++ err)
      Right procT -> Right (TReplication procT)
typeCheckPiProcess (Match pi1 pi2 piProPrime) = case typeCheckPi pi1 of
      Left err   -> Left ("term 'Match' type fail on first pi argument: " ++ err)
      Right tpi1 -> case typeCheckPi pi2 of
         Left err   -> Left ("term 'Match' type fail on second pi argument: " ++ err)
         Right tpi2 -> case typeCheckPiProcess piProPrime of
            Left err     -> Left ("term 'Match' type fail on process subterm: " ++ err)
            Right primeT -> Right (TMatch primeT) 
typeCheckPiProcess Nil = Right TNil
typeCheckPiProcess (Let (pi1,pi2) pairPossibly proc) = case typeCheckPi pairPossibly of
      (Right pairPossiblyT) -> if acceptablePi (TPair TZero TZero) pairPossiblyT then
                                 case (typeCheckPi pi1, typeCheckPi pi2) of
                                    (Right TVar, Right TVar) -> case typeCheckPiProcess proc of
                                                   (Right procT) -> Right (TLet procT)
                                                   (Left err)    -> Left ("Type error in Let subprocess: " ++ err)
                                    (tup)                    -> Left ("Type error. Expected 2 variables in let binding. Found: " ++ join (map (either show show) (listify2 tup)) )           
                                else Left ("Type error. Expected type Tpair in Let binding. Actual type: " ++ (show pairPossiblyT))    
      (Left err)            -> Left ("Type error in pair value of Let: " ++ err)                                
typeCheckPiProcess (Case pi0 pi1 piproc1 pi2 piproc2) = if(and (map isOKnumberPi [pi0,pi1,pi2])) 
 then
  case (typeCheckPi pi0, typeCheckPi pi1, typeCheckPi pi2) of
      (Right pi0T, Right pi1T, Right pi2T) -> case typeCheckPiProcess piproc1 of
                                                (Right piproc1T) -> case typeCheckPiProcess piproc2 of
                                                                     (Right piproc2T) -> Right TCase
                                                                     (Left err)       -> Left ("Type Error in second process of Case: " ++ err)
                                                (Left err)       -> Left ("Type Error in first process of Case: " ++ err)
      triplet                              -> Left ("Error in a pi term of Case statement. Actual types: " ++ join ((map (either show show) (listify3 triplet))))
 else Left ("Type Error. Case of non-numberic types. pi0: " ++ (show pi0) ++ ", " ++ (show pi1) ++ ", " ++ (show pi2))
typeCheckPiProcess (Chain procs) = let types = map typeCheckPiProcess procs in
                                    case foldr (\eitherType ansList -> 
                                                   case eitherType of 
                                                        l@(Left err) -> l:ansList
                                                        (Right _) -> ansList) [] types of
                                         []   -> Right (TChain (map (either (const TNil) id) types)) --note this is safe since we have established they are ALL right side
                                         errs -> Left ("The following errors were found in Chain:\n\t" ++ (join (map (\a -> (show a) ++ "\n\t") errs)))
                              
                                    
acceptablePi :: PiType -> PiType -> Bool
acceptablePi (TPair _ _) type2 = case type2 of
                                  (TPair _ _) -> True
                                  (TVar)      -> True
                                  _           -> False
acceptablePi (TName) type2 = case type2 of
                                   (TName) -> True
                                   (TVar)  -> True
                                   _       -> False
isOKnumberPi :: Pi -> Bool
isOKnumberPi Zero   = True
isOKnumberPi (Succ pi) = if isOKnumberPi pi then True
                                          else False
isOKnumberPi (Var _) = True                                          
isOKnumberPi _       = False                                      
                     
listify2 :: (a,a) -> [a]
listify2 (x,y) = [x,y]

listify3 :: (a,a,a) -> [a]
listify3 (x,y,z) = [x,y,z]

                                                                                                                                                                                      
-- Pi example 2.3.1
a_m = Output (Name "C_ab") Zero Nil --A(M) sends zero on channel AB
b   = Chain [(Input (Name "C_ab") (Var "x") Nil), Restriction (Var "x") Nil]
inst_m = Restriction (Name "C_ab") (Composition a_m b)

badchain = Chain [ badpieProc, a_m, a_m,badpieProc, b]

data GammaMembers = VarBind (Pi, Pi)
                  | Restricted Pi
                  | Message Pi Pi deriving (Show, Eq)
type Gamma = [GammaMembers]
type GlobalChannels = (TVar [(Pi,MVar Pi)]) 
type MyStateT a = StateT (Gamma, GlobalChannels) IO a


--mystateT = 
{-

typeandReduce :: PiProcess -> Either String PiProcess
typeandReduce piproc = case typeCheckPiProcess piproc of
                            Left err -> Left ("TYPE ERROR: " ++ err)
                            Right t  -> reduce piproc
                            -}

runReduce :: PiProcess -> IO (PiProcess, (Gamma,GlobalChannels))
runReduce piProc =  do 
                     emtyTVar <-newTVarIO []
                     x <- (runStateT (reduce piProc)) ([],emtyTVar)
                    -- print x
                     return x
-- 
test = Restriction (Var "varname") (Restriction (Var "varname2") Nil) 

{---PiProcess       
data PiProcess = Output Pi Pi PiProcess
               | Input Pi (Pi) PiProcess --Input Pi (Var String) PiProcess
               | Composition PiProcess PiProcess
               | Restriction (Pi) PiProcess --Restriction (Name String) PiProcess
               | Replication PiProcess
               | Match Pi Pi PiProcess
               | Nil
               | Let (Pi,Pi) Pi PiProcess
               | Case Pi Pi PiProcess Pi PiProcess 
               | Chain [PiProcess] deriving (Show, Eq)-}
addMessage' :: Pi -> Pi -> [(Pi,MVar Pi)] -> IO [(Pi,MVar Pi)]
addMessage' pi1 pi2 [] = do 
                           mvar <- newMVar pi2
                           return [(pi1,mvar)]
addMessage' pi1 pi2 (x:xs) = if pi1 == (fst x) then
                                 do
                                    takeMVar (snd x)
                                    putMVar (snd x) pi2
                                    return (x:xs)
                             else
                                 do
                                    r <- addMessage' pi1 pi2 xs
                                    return ([x] ++ r)

addMessage :: Pi -> Pi -> [(Pi,MVar Pi)] ->  [(Pi,MVar Pi)]
addMessage pi1 pi2 xs = unsafePerformIO $ addMessage' pi1 pi2 xs

                            

isPresent ::  Pi -> [(Pi,MVar Pi)] -> Bool
isPresent _ []  = False
isPresent t (x:xs) = if t == (fst x) then True else isPresent t xs

findMVar ::  Pi -> [(Pi,MVar Pi)] -> Maybe (MVar Pi) 
findMVar pi1 [] = Nothing
findMVar pi1 (x:xs) -> if pi1 == (fst x) then Just (snd x)
                                         else findMVar pi1 xs
 
 
reduce :: PiProcess ->  MyStateT PiProcess
reduce (Composition proc1 proc2)  = do
                                                
                              reduce Nil 
                              
reduce (Output pi1 pi2 piproc)   = do
                              s <- get
                              let tvarList = snd s
                              --tvarListUnwraped <-readTVarIO tvarListd
                             -- if isPresent then 
                              liftIO $ atomically $ do 
                                                      (modifyTVar tvarList (addMessage pi1 pi2))
--                               globalStateList <-liftIO $ readIORef ioRefList
--                               newglob <-liftIO $ addMessage pi1 pi2 globalStateList
--                               put (fst s, 
                              --let f <- (addMessage pi1 pi2)
                              --liftIO (modifyIORef ioRefList f )
                              
                              reduce piproc
                              --withStateT (addMessage pi1 pi2) (reduce piproc) -- update the state and continue.
                               
reduce (Input pi1 pi2 piproc)   = do
                              s <- get
                              let tvarList = snd s
                              tvarListUnwrapped <- readTVarIO
                              case findpair pi1 tvarListUnwraped of
                                   Just mvar -> do
                                      val <- takeMVar mvar
                                      
                                   Nothing -> liftIO $ atomically $ do 
                                                      (modifyTVar tvarList (addMessage pi1 pi2))
                              
                              
                              reduce piproc                              
reduce (Restriction pi1 piproc)  = do
                              s <- get
                              let s' =  ( (Restricted pi1 : (fst s)), snd s)            
                              put s'
                              reduce piproc 
reduce (Match pi1 pi2 piproc)    = do
                              if pi1 == pi2 then reduce piproc
                                            else return Stuck
reduce (Let (pi1, pi2) pi3 piproc) = do
                              s <- get
                              case (pi1,pi2,pi3) of
                                   (v1@(Var var1),v2@(Var var2),(Pair p1 p2))-> do
                                      put ((VarBind (v1,p1)):(VarBind (v2,p2)):(fst s), snd s)
                                      reduce piproc
                                   (_) -> return Stuck
reduce (Case pi0 pi1 piproc1 pi2 piproc2) = do
                              s <- get
                              if pi0 == pi1 then reduce piproc1
                                            else if pi0 == pi2 then reduce piproc2
                                                               else return Stuck                              
reduce (Chain procs) = do                       
                        case procs of                            
                            []     -> return Stuck
                            (x:xs) -> do
                              r <- reduce x
                              newState <- get
                              case r of
                                   Stuck -> return Stuck
                                   _     -> reduce (Chain xs)
                               
reduce Nil  = return Nil                              

                 