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
    | Var String 
	| Encryption Pi Pi deriving (Show, Eq)        
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
               | Stuck deriving (Show, Eq)

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
                   | TChain [PiProcessType] deriving (Eq, Show)
        




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
typeCheckPi (Encryption pi1 pi2) =  case typeCheckPi pi1 of
                                        Left err   -> Left err
                                        Right pi1T -> case typeCheckPi pi2 of
                                                        Left err -> Left err
                                                        Right pi2T -> Right TEncryption														
typeCheckPi x = Left ("Type failure: " ++ (show x))


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
typeCheckPiProcess (Value val)   = Right TValue 
typeCheckPiProcess (OrderedOutput _ from to pi piproc)   = typeCheckPiProcess (Output (Name ("C_" ++ from ++ to)) pi piproc)
typeCheckPiProcess (CaseDecrypt encrytped var key piproc) = case typeCheckPi encrytped of
                                                         (Right TEncryption) -> case typeCheckPi var of
                                                                                (Right TVar) -> case typeCheckPi key of
                                                                                                    (Right keyT) -> case typeCheckPiProcess piproc of
																									                     (Right piprocT) -> Right (TCaseDecryption piprocT)
																									                     (Left err ) -> Left err
                                                                                                    (Left err) -> Left ("TYPE ERROR in CaseDecrypt key: " ++ err)
                                                                                (Right otherT) -> Left ("TYPE ERROR. Expected Var type in CaseDecrypt but found: " ++ (show otherT))
                                                                                (Left err) -> Left err
                                                         (Right TVar) -> case typeCheckPi var of
                                                                                (Right TVar) -> case typeCheckPi key of
                                                                                                    (Right keyT) -> case typeCheckPiProcess piproc of
																									                     (Right piprocT) -> Right (TCaseDecryption piprocT)
																									                     (Left err ) -> Left err
                                                                                                    (Left err) -> Left ("TYPE ERROR in CaseDecrypt key: " ++ err)
                                                                                (Right otherT) -> Left ("TYPE ERROR. Expected Var type in CaseDecrypt but found: " ++ (show otherT))
                                                                                (Left err) -> Left err
                                                         (Right other) -> Left ("TYPE ERROR. Expected TEncryption type in CaseDecrypt but found: " ++ (show other))
                                                         (Left err)    -> Left err
																																													
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

data GammaMembers = VarBind (Pi, Pi)
                  | Restricted Pi
                  | Mess Pi Pi deriving (Show, Eq)
type Gamma = [GammaMembers]
type GlobalChannels = (TVar [(Pi,MVar Pi)]) 
type MyStateT a = StateT (Gamma, GlobalChannels) IO a


--mystateT = 
typeandReduce :: PiProcess -> IO () --Either String PiProcess
typeandReduce piproc = case typeCheckPiProcess piproc of
                            Left err -> do
							              putStrLn (("TYPE ERROR: " ++ err));
										  putStrLn "";
										  putStrLn "";
										  return ()
                            Right t  -> do
										  putStrLn "PASSED TYPE CHECKER."
										  putStrLn "TYPE:"
										  print t 
										  putStrLn ""
										  runReduceShow piproc
data Result = Result {
						finalpiproc :: PiProcess,
						gamma       :: Gamma,
						piproctype  :: PiProcessType
					  } deriving (Eq, Show)
					  
					  
runForOutput :: PiProcess ->IO (Either String Result )
runForOutput piproc = do
                        case typeCheckPiProcess piproc of
                            Left err -> return (Left ("TYPE ERROR: " ++ err))	              
                            Right t  -> do
										  --putStrLn "PASSED TYPE CHECKER."
										  --putStrLn "TYPE:"
										  --print t 
										  --putStrLn ""
										  --runReduceShow piproc
							              x <- runReduce piproc
							              let gamgam = fst (snd x)
							              return (Right (Result (fst x) gamgam t))
						
runReduceShow term= do
					putStrLn "BEGINNING REDUCTION"                    
					x <- runReduce term
					putStrLn "RESULT:"
					print (fst x)
					s <- readTVarIO (snd (snd x))
					let gamma = fst(snd x)
					putStrLn ("Gamma: " ++ (show gamma))
					print "END"
runReduce :: PiProcess -> IO (PiProcess, (Gamma,GlobalChannels))
runReduce piProc =  do 
                     emtyTVar <-newTVarIO []
                     x <- (runStateT (reduce piProc)) ([],emtyTVar)
                    -- print x
                     return x
-- 


addMessage' :: Pi -> Pi -> [(Pi,MVar Pi)] -> IO [(Pi,MVar Pi)]
addMessage' pi1 pi2 [] = do 
                           mvar <- newMVar pi2
                           return [(pi1,mvar)]
addMessage' pi1 pi2 (x:xs) = if pi1 == (fst x) then
                                 do
									maybeTake <- tryTakeMVar (snd x) -- this takes the value if there was one. We throw this away. 
									--takeMVar (snd x)
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
findMVar pi1 (x:xs) = if pi1 == (fst x) then Just (snd x)
                                         else findMVar pi1 xs

printer = newMVar (1 :: Int)
reduce :: PiProcess ->  MyStateT PiProcess
reduce (Composition proc1 proc2)  = do
                                      m1 <- liftIO newEmptyMVar
                                      m2 <- liftIO newEmptyMVar
                                      tid <- liftIO ( forkIO (do
																--print "efe"
																p1 <- return (reduce proc1)
																putMVar m1 p1
																
																--print "Done 1"
																))
                                      tid2 <- liftIO ( forkIO (do
																--print "efe"
																p2 <- return (reduce proc2)
																putMVar m2 p2
																--myPrinter <- printer
																--takeMVar myPrinter
																--putStrLn "Done 2"
																--putMVar myPrinter 1
																))
                                      p1res <- liftIO $ takeMVar m1
                                      p2res <- liftIO $ takeMVar m2
                                      pi1res2 <- p1res
                                      pi2res2 <- p2res
                                      return (Composition pi1res2 pi2res2) --(Composition p1res p2res)                            
reduce (Output pi1' pi2' piproc)   = do
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              s <- get
                              let tvarList = snd s 
                              liftIO $ atomically $ do 
                                                      (modifyTVar tvarList (addMessage pi1 pi2))
                              reduce piproc
reduce (OrderedOutput _ from to pi piproc) = reduce (Output (Name ("C_" ++ from ++ to)) pi piproc)							  
reduce (Input pi1' pi2 piproc)   = do
                              pi1 <- subIfVar pi1'     
                              --pi2 is of course a variable.
                              s <- get
                              let tvarList = snd s
                              tvarListUnwrapped <-liftIO $ readTVarIO tvarList
                              case findMVar pi1 tvarListUnwrapped of
                                   Nothing -> do
												liftIO (putStrLn "I didn't find that mvar so now I have to create one.")
												mvar <- liftIO $ newEmptyMVar -- pi2
												let pair = (pi1,mvar)
												liftIO $ atomically $ (modifyTVar tvarList (\list -> pair : list))
                                   Just v  -> do
												liftIO (putStrLn ("In Input. MVar was found so I can continue without adding an empty mvar to state"))												
                              tvarListUnwrapped' <-liftIO $ readTVarIO tvarList --do I need to do this again?
                              case findMVar pi1 tvarListUnwrapped' of
								Just mvar -> do
												val <-liftIO $ takeMVar mvar -- we block until we get a message
												s <- get
												put ((VarBind (pi2, val)):(fst s),snd s) -- update the state to have this variable
												liftIO $ putMVar mvar val -- put the value back because anyone can read the channel multiple times. hopefully this doesn't break outputing to that channel a second time. 
												--piproc' <- substituteAllInstancesOf pi2 val piproc
												reduce piproc -- finally do the next process.
								Nothing -> return Stuck -- this should not possibly happen. We either block, or put a new mvar in the state to block on.                              
reduce (Restriction pi1 piproc)  = do
                              s <- get                        
                              let s' =  ( (Restricted pi1 : (fst s)), snd s)            
                              put s'
                              reduce piproc 
reduce (Match pi1' pi2' piproc)    = do
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              if pi1 == pi2 then reduce piproc
                                            else return Stuck
reduce (Let (pi1, pi2) pi3' piproc) = do
                              pi3 <- subIfVar pi3'
                              s <- get
                              case (pi1,pi2,pi3) of
                                   (v1@(Var var1),v2@(Var var2),(Pair p1 p2))-> do
                                      put ((VarBind (v1,p1)):(VarBind (v2,p2)):(fst s), snd s)
                                      reduce piproc
                                   (_) -> return Stuck
reduce (Case pi0' pi1' piproc1 pi2' piproc2) = do
                              pi0 <- subIfVar pi0'
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              s <- get
                              if pi0 == pi1 then reduce piproc1
                                            else if pi0 == pi2 then reduce piproc2
                                                               else return Stuck                              
reduce (Chain procs) = do                       
                        case procs of                            
                            []     -> return EmptyChain
                            (x:xs) -> do
                              liftIO $ print x
                              r <- reduce x
                              liftIO $ putStrLn ("r: " ++ (show r))							  
                              newState <- get
                              case r of
                                   Stuck -> return Stuck
                                   _     -> reduce (Chain xs)                               
reduce Nil  = return Nil
reduce (Value pi') = do
                     pi <- subIfVar pi'
                     return (Value pi)
reduce (CaseDecrypt encrypted' var key' piproc) = do
													encrypted <- subIfVar encrypted'
													key <- subIfVar key'
													case encrypted of
														(Encryption mess keyin) -> if keyin == key then do
																										s <- get
																										put ((VarBind (var, mess)):(fst s),snd s) -- update the state to have this variable
																										reduce piproc
																								   else return Stuck
														(_) -> return Stuck
subIfVar :: Pi -> MyStateT Pi
subIfVar pi = do
               s <- get
               let gamma = fst s
               case myLookup pi gamma of
                    Nothing -> return pi
                    Just val -> return val
subIfVar' :: Pi -> Gamma -> Pi
subIfVar' pi gamma = case myLookup pi gamma of
                      Nothing -> pi
                      Just val -> val
                    
myLookup :: Pi -> Gamma -> Maybe Pi
myLookup pi []     = Nothing
myLookup pi (t:xs) = case t of
                          VarBind (x,y) -> if x == pi then return y else myLookup pi xs 
                          _ -> myLookup pi xs


						  
						  
						  
examplePiVALID = Pair (Succ (Succ (Succ Zero))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
examplePiVALIDSuccVar = Pair (Succ (Succ (Succ (Var "varhere1")))) (Pair (Name "namehere") (Pair Zero (Var "varhere"))) --demonstrates succ (Variable) is valid.
examplePiINVALIDSucc = Pair (Succ (Succ (Succ (Name "name")))) (Pair (Name "namehere") (Pair Zero (Name "varhere")))	  -- demonstrates succ (non-number , non-variable) invalid


piprocINVALIDOutoutToNonChan = Output Zero Zero Nil   --tries to output a channel that is NOT a name.            
piprocVALIDOutput            = Output (Name "channel") (Name "message") Nil
piprocVALIDInput             = Input (Name "channel") (Name "message") Nil
piprocVALIDComposition = Composition piprocVALIDOutput piprocVALIDInput
piprocINVALIDChain = Chain [ piprocINVALIDOutoutToNonChan, a_m231, a_m231,piprocINVALIDOutoutToNonChan, b231]
piprocVALIDRestriction = Restriction (Var "varname") (Restriction (Var "varname2") Nil)
piprocVALIDCase = Case Zero (Succ Zero) (Value (Name "Shouldn't get here")) Zero (Value (Name "Should get here"))  --demonstrates proper Case reducing
piprocVALIDCaseWVariable = Case Zero (Var "variablename") (Value (Name "Shouldn't get here")) Zero (Value (Name "Should get here"))
piprocINVALIDCaseNonNumber = Case (Name "num should be here or Var") Zero (Value (Name "Shouldn't get here")) (Succ Zero) (Value (Name "Shouldn't get here")) 
piprocINVALIDCaseStuck = Case Zero (Succ Zero) (Value (Name "Shouldn't get here")) (Succ Zero) (Value (Name "Shouldn't get here")) 
                                                                                                                                                                                       
-- PiProc example 2.3.1
a_m231 = Output (Name "C_ab") Zero Nil --A(M) sends zero on channel AB
b231   = Input (Name "C_ab") (Var "x") (Restriction (Var "x") Nil)
inst_m231 = Restriction (Name "C_ab") (Composition a_m231 b231)

a_m231BADChan = Output (Name "C_az") Zero Nil --A(M) sends zero on channel AB
b231BADChan   = Input (Name "C_ab") (Var "x") (Restriction (Var "x") Nil)
inst_m231BADChan = Restriction (Name "C_ab") (Composition a_m231BADChan b231BADChan)
 
						  
--page 13 example protocol
a_m2 = Restriction (Name "C_ab") (Output (Name "C_as") (Name "C_ab") (Output (Name "C_ab") (Name "Message from a to b should be here") Nil))
s    = Input (Name "C_as") (Var "x") (Output (Name "C_sb") (Var "x") Nil)
b2   = Input (Name "C_sb") (Var "x") (Input (Var "x") (Var "messageFromA") Nil) --(Input (Var "xb") (Var "messageFromA") Nil)
inst_m2 = Restriction (Name "C_as") (Restriction (Name "C_sb") (Composition a_m2 (Composition s b2)))
-- this is same as above page 13 example proto, but shows the value received at the end.
a_m2'    = Restriction (Name "C_ab") (Output (Name "C_as") (Name "C_ab") (Output (Name "C_ab") (Name "Message from a to b should be here") Nil))
s'       = Input (Name "C_as") (Var "x") (Output (Name "C_sb") (Var "x") (Value (Var "x")))
b2'      = Input (Name "C_sb") (Var "x") (Input (Var "x") (Var "messageFromA") (Value (Var "messageFromA"))) --(Input (Var "xb") (Var "messageFromA") Nil)
inst_m2' = Restriction (Name "C_as") (Restriction (Name "C_sb") (Composition a_m2' (Composition s' b2')))