{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
--pi calculus language
module ISpi where


import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TMVar
import System.IO.Unsafe

import Data.List
import qualified GHC.Conc as C
import Control.DeepSeq


printTMVarStuff x = do
                    str <- printTMVarStuff' x
                    putStrLn str
                    
printTMVarStuff' :: [(Pi,MVar Pi)] -> IO String
printTMVarStuff' [] = return ""
printTMVarStuff' (x:xs) = do
                        content <- takeMVar (snd x)
                        putMVar (snd x) content
                        rest <- printTMVarStuff' xs
                        return ("(" ++ (show (fst x)) ++ ", " ++ (show content) ++ ")\n" ++ rest )
                        
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
                      s <- atomically $ readTMVar (snd (snd x))
                      let gamma = fst(snd x)
                      putStrLn ("Gamma: " ++ (show gamma))
                      print "END"
runReduce :: PiProcess -> IO (PiProcess, (Gamma,GlobalChannels))
runReduce piProc =  do 
                     emtyTMVar <-newTMVarIO []
                     x <- (runStateT (reduce piProc)) ([],emtyTMVar)
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
                                      s <- get
                                      m1 <- liftIO newEmptyMVar
                                      m2 <- liftIO newEmptyMVar
                                      liftIO ( do forkIO (do
                                                         --print "~~~~~~~~~~~~~~~"
                                                         --p1 <- return (force (reduce proc1))
                                                         p1 <-runStateT (reduce proc1) s
                                                         --print "#"
                                                         print (fst p1)
                                                         putMVar m1 p1
                                                         
                                                         --print "Done 1"
                                                         )
                                                  forkIO (do
                                                         --print $ "second fork: "
                                                         --print "^^^^^^^^^^^^^"
                                                         --p2 <- return (force (reduce proc2))
                                                         yield
                                                         p2 <-runStateT (reduce proc2) s
                                                         --print (fst p2)
                                                         --print ("hhhhhhhhhhhhHHHHHHHHHHHHHH: ") -- ++ (show (fst p2)))
                                                         
                                                         putMVar m2 p2
                                                         
                                                         --myPrinter <- printer
                                                         --takeMVar myPrinter
                                                         --putStrLn "Done 2"
                                                         --putMVar myPrinter 1
                                                         )
                                          )
--                                       liftIO ( forkIO (do
--                                           print "second fork"
--                                           p2 <- return (reduce proc2)
--                                           putMVar m2 p2
--                                           --myPrinter <- printer
--                                           --takeMVar myPrinter
--                                           --putStrLn "Done 2"
--                                           --putMVar myPrinter 1
--                                           ))
                                      p1res <- liftIO $ takeMVar m1
                                      p2res <- liftIO $ takeMVar m2
                                      --pi1res2 <- p1res
                                      --pi2res2 <- p2res
                                      --pi2res2 <- p1res
                                      s <- get
                                      tmvar <- liftIO $ atomically $ readTMVar (snd s)
                                      liftIO $ print "TMVAR contents"
                                      liftIO $ printTMVarStuff (tmvar)
                                      return (Composition (fst p2res) (fst p2res)) --(Composition p1res p2res)                            
reduce (Output pi1' pi2' piproc)   = do
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              liftIO $ putStrLn ("OUTPUT: " ++ (show pi1))
                              s <- get
                              let tmvarList = snd s 
                              liftIO $ atomically $ do 
                                                      (modifyTVar tmvarList (addMessage pi1 pi2))
                              reduce piproc
reduce (OrderedOutput _ from to pi piproc) = reduce (Output (Name ("C_" ++ (if from < to then (from ++ to) else (to ++ from)))) pi piproc)							  
reduce (Input pi1' pi2 piproc)   = do  
                              --liftIO $ putStrLn ("INPUT: " ++ (show pi1'))
                              pi1 <- subIfVar pi1'     
                              
                              --pi2 is of course a variable.
                              s <- get
                              let tmvarList = snd s
                              tmvarListUnwrapped <-liftIO $ atomically $ readTMVar tmvarList
                                  
                              case findMVar pi1 tmvarListUnwrapped of
                                  Nothing -> do
                                     --liftIO (putStrLn ("I didn't find that mvar so now I have to create one. No Mvar associated with: " ++ (show pi1)))
                                     mvar <- liftIO $ newEmptyMVar -- pi2
                                     --let pair = (pi1,mvar)
                                     liftIO $ atomically $ do
                                                            --mvar <- newEmptyMVar -- pi2
                                                            let pair = (pi1,mvar)
                                                            swapTMVar tmvarList (pair : tmvarListUnwrapped)
                                                            return ()
                                                            --(modifyTVar tmvarList (\list -> pair : list))                                     
                                  Just v  -> do return ()
                                     --liftIO (putStrLn ("In Input. MVar was found so I can continue without adding an empty mvar to state"))												
                              tmvarListUnwrapped' <-liftIO $ atomically $ readTMVar tmvarList --do I need to do this again?                              
                              case findMVar pi1 tmvarListUnwrapped' of
                                                                Just mvar -> do       
                                                                  --liftIO yield
                                                                  liftIO (myPrint ("$$$$$$$B:" ++ (show pi1)))
                                                                  --liftIO $ myPrint "&&&&&&&&&&&&&&&7"
                                                                  val <-liftIO $ takeMVar mvar -- we block until we get a message  
                                                                 -- liftIO (print ("GGGGGGGGGB:" ++ (show val)))
                                                                  --liftIO $ print "I never get to happen   EITHER" 
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
                     case pi of
                          p@(Pair x y) -> do -- I need to recursively lookup variables.
                                             (Value v1) <- reduce (Value x) 
                                             (Value v2) <- reduce (Value y)
                                             return (Value (Pair v1 v2))
                          notAPair     -> return (Value pi)
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
subIfVar' (Pair x y) gamma = Pair (subIfVar' x gamma) (subIfVar' y gamma) --added this. def needed.
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

myPrint :: String -> IO ()
myPrint str = do
                atomically $ C.unsafeIOToSTM (print str)
                return ()
--our protocol
--appraiser
armored_a = OrderedOutput 1 "a" "b" (Name "InitRequestTOAttester") 
            (Input (Name "C_ab") (Var "fromAtt1") 
            (Input (Name "C_ab") (Var "fromAtt2") 
            (Value (Pair (Var "fromAtt1") (Var "fromAtt2")))))
--attester
armored_b = Input (Name "C_ab") (Var "ReqFromApp") 
            (OrderedOutput 2 "b" "c" (Name "b + AIK") 
            (Input (Name "C_bc") (Var "CAResponseToAtt") 
            (OrderedOutput 4 "b" "m" (Name "pleasegiveMeas1") 
            (Input (Name "C_bm") (Var "measurementFromMeas") 
            (OrderedOutput 6 "b" "a" (Var "CAResponseToAtt") 
            (OrderedOutput 7 "b" "a" (Var "measurementFromMeas") (Value (Pair (Var "ReqFromApp") (Pair (Var "CAResponseToAtt") (Var "measurementFromMeas"))))))))))
armored_c = Input (Name "C_bc") (Var "reqToCA")
            (OrderedOutput 3 "c" "b" (Name "pretend this is a CA cert") (Value (Var "reqToCA")))
armored_m = Input (Name "C_bm") (Var "desE")
            (OrderedOutput 5 "m" "b" (Name "pretend this is evidence") (Value (Var "desE")))
inst_armored =Restriction (Name "C_bm")
              (Restriction (Name "C_ab")
              (Composition armored_a (Composition armored_b (Composition armored_c armored_m))))
              
              
              
examplewhyBroken_a = Output (Name "C_ab") (Name "Hello") 
                    (Input (Name "C_ab") (Var "x") (Value (Var "x"))) 
                    
examplewhyBroken_b = Input (Name "C_ab") (Var "x") 
                    (Output (Name "C_ab") (Pair (Var "x") (Var "x")) 
                     Nil)
inst_broken = Restriction (Name "C_ab") (Composition examplewhyBroken_a examplewhyBroken_b)

examplewhyBroken_a' = Output (Name "C_ab") (Name "Hello") 
                    (Input (Name "C_ba") (Var "x") 
                    (Input (Name "C_ba") (Var "y")
                    (Value (Pair (Var "x") (Var "y"))))) 
                    
examplewhyBroken_b' = Input (Name "C_ab") (Var "x") 
                    (Output (Name "C_ba") (Name "poop") --(Pair (Var "x") (Var "x"))
                    (Output (Name "C_ba") (Name "Have a nice day Mr. A!")
                     Nil))
inst_broken' = Restriction (Name "C_ab") (Composition examplewhyBroken_a' examplewhyBroken_b')


examplewhyBroken_af = Output (Name "C_ab") (Name "Hello") 
                    (Input (Name "C_ab") (Var "x") (Value (Var "x"))) 
                    
examplewhyBroken_bf = Input (Name "C_ab") (Var "x") 
                    (Output (Name "C_ba") ((Var "x")) 
                     Nil)
inst_brokenf = Restriction (Name "C_ab") (Composition examplewhyBroken_af examplewhyBroken_bf)
