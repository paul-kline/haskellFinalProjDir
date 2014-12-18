{-# LANGUAGE RecordWildCards  #-}
module ISpi2 where

import SpiTypeChecker
import SpiTypes
import Control.Concurrent.STM
import Control.Concurrent.STM.TMVar
import Control.Monad.State.Strict
import Control.Monad
import Control.Concurrent.MVar
import Control.Concurrent
import Data.List
import Data.IORef

canReadOwn = False
canReReceive= False
canBroadcast = True



runReduce :: PiProcess ->IO (PiProcess, MyState)
runReduce piproc = do
                    myemtpyTMVar <- newTMVarIO (emptyPiMVarPairList)
                    starterID <- newMVar (0 :: Int)
                    let s0 = MyState {gamma =[], globalChans= myemtpyTMVar, usedIDs = [], globID = starterID}
                    runStateT (reduce piproc) s0

reduce :: PiProcess -> MyStateTMonad PiProcess
reduce (Composition proc1 proc2)  = do
                                     mv1 <- liftIO $ newEmptyMVar
                                     mv2 <- liftIO $ newEmptyMVar
                                     s <- get
                                     liftIO $ do                                                  
                                                  forkIO $ do
                                                         --print "~~~~~~~~~~~~~~~"
                                                         --p1 <- return (force (reduce proc1))
                                                         p1 <-runStateT (reduce proc1) s
                                                         --print "#"
                                                         print (fst p1)
                                                         putMVar mv1 p1
                                                         
                                                  forkIO $ do
                                                         --print $ "second fork: "
                                                         --print "^^^^^^^^^^^^^"
                                                         --p2 <- return (force (reduce proc2))
                                                         --yield
                                                         p2 <-runStateT (reduce proc2) s
                                                         print (fst p2)
                                                         --print ("hhhhhhhhhhhhHHHHHHHHHHHHHH: ") -- ++ (show (fst p2)))
                                                         
                                                         putMVar mv2 p2
                                                         
                                                         --myPrinter <- printer
                                                         --takeMVar myPrinter
                                                         --putStrLn "Done 2"
                                                         --putMVar myPrinter 1
                                     
                                     res1 <- liftIO $ takeMVar mv1
                                     res2 <- liftIO $ takeMVar mv2
                                     (MyState x y ls m) <- get
                                     let res1gamma = gamma (snd res1)
                                     let res2gamma = gamma (snd res2)
                                     put (MyState (union res1gamma res2gamma) y ls m)
                                     return (Composition (fst res1) (fst res2))
reduce (Output pi1' pi2' piproc)   = do
                                      pi1 <- subIfVar pi1'
                                      pi2 <- subIfVar pi2'
                                      (MyState gam tmvar ls m) <- get
                                      --tmvarContents :: [(Pi,MVar Pi,Int)]
                                      tmvarContents <- liftIO $ atomically $ takeTMVar tmvar
                                      case findMVar pi1 tmvarContents of
                                        Nothing -> do
                                                    mID <- getMessageID
                                                    mvr <-liftIO $ newMVar (pi2,mID)
                                                    let tmvarContents' = (pi1,mvr):tmvarContents
                                                    if canReadOwn then return ()
                                                                      else do
                                                                            let ls' = mID:ls
                                                                            liftIO $ putStrLn ("new mess ID:" ++ (show mID))
                                                                            put (MyState gam tmvar ls' m)
                                                    liftIO $ atomically $ putTMVar tmvar tmvarContents'
                                        Just pimvar -> do
                                                        maybemvrC <- liftIO $ tryTakeMVar pimvar --leaves the MVar empty no matter what.
                                                        replacementID <- getMessageID
                                                        liftIO $ putMVar pimvar (pi2, replacementID)
                                                        if canReadOwn then return ()
                                                                      else do
                                                                            let ls' = replacementID:ls
                                                                            liftIO $ putStrLn ("ID:" ++ (show replacementID))
                                                                            put (MyState gam tmvar ls' m)
                                                        liftIO $ atomically $ putTMVar tmvar tmvarContents
                                                        
                                      --at this point we have put the message out there and can continue
                                      --put the TMVar back.
                                      --liftIO $ putStrLn ("OUTPUT ON: " ++ (show pi1) ++ "::" ++ (show pi2))
                                      --liftIO yield
                                      reduce piproc
reduce (OrderedOutput _ from to pi piproc) = reduce (Output (Name ("C_" ++ (if from < to then (from ++ to) else (to ++ from)))) pi piproc)
reduce (Input pi1' pi2 piproc)   = do 
                                    pi1 <- subIfVar pi1'
                                    (MyState gam tmvarP ls m) <- get
                                    tmvarC <- liftIO $ atomically $ takeTMVar tmvarP
                                  --tmvarC :: [(Pi,MVar Pi)]
                                    liftIO $ putStrLn ("IN:" ++ (show (Input pi1 pi2 piproc)))
                                    case findMVar pi1 tmvarC of
                                        Nothing -> do
                                                    mvr <-liftIO $ newEmptyMVar
                                                    let tmvarContents' = (pi1,mvr):tmvarC
                                                    liftIO $ atomically $ putTMVar tmvarP tmvarContents'
                                                    liftIO $ yield
                                        Just mvr -> do
                                                        liftIO $ atomically $ putTMVar tmvarP tmvarC
                                    --whether or not I had to put an emptyMVar there, it's there and TMVAR can be taken
                                    tmvarC' <- liftIO $ atomically $ readTMVar tmvarP --non blocking
                                    case findMVar pi1 tmvarC' of
                                        Nothing     -> liftIO $ putStrLn "This should never happen ever. ever ever."
                                        Just pimvar -> do 
                                                        inputMessage <- if canReReceive then liftIO $ takeMVar pimvar
                                                                                        else waitForFresh pimvar 0
                                                        --inputMessage <-liftIO $ takeMVar pimvar
                                                        let ls' = (snd inputMessage) : ls
                                                        let piMess = fst inputMessage
                                                        (MyState gam tmvP ls m) <- get
                                                        let gam' = (VarBind (pi2, piMess)):gam
                                                        put (MyState gam' tmvP ls' m)
                                                        if canBroadcast then do liftIO $ tryPutMVar pimvar inputMessage
                                                                                return ()
                                                                        else return ()
                                                        
                                    reduce piproc                 
reduce (Restriction pi1 piproc)  = do
                              (MyState g globs ls m) <- get                                                                 
                              put (MyState {gamma =(Restricted pi1 :g), globalChans=globs, globID = m, usedIDs = ls})                              
                              reduce piproc 
reduce (Match pi1' pi2' piproc)    = do
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              if pi1 == pi2 then reduce piproc
                                            else return Stuck
reduce (Let (pi1, pi2) pi3' piproc) = do
                              pi3 <- subIfVar pi3'
                              --s <- get
                              case (pi1,pi2,pi3) of
                                   (v1@(Var var1),v2@(Var var2),(Pair p1 p2))-> do
                                      --put ((VarBind (v1,p1)):(VarBind (v2,p2)):(fst s), snd s)
                                      reduce piproc
                                   (_) -> return Stuck
reduce (Case pi0' pi1' piproc1 pi2' piproc2) = do
                              pi0 <- subIfVar pi0'
                              pi1 <- subIfVar pi1'
                              pi2 <- subIfVar pi2'
                              --s <- get
                              if pi0 == pi1 then reduce piproc1
                                            else if pi0 == pi2 then reduce piproc2
                                                               else return Stuck                              
reduce (Chain procs) = do                       
                        case procs of                            
                            []     -> return EmptyChain
                            (x:xs) -> do
                              --liftIO $ print x
                              r <- reduce x
                             -- liftIO $ putStrLn ("r: " ++ (show r))							  
                              --newState <- get
                              case r of
                                   Stuck -> return Stuck
                                   _     -> reduce (Chain xs)                               
reduce Nil  = return Nil
reduce (Value pi') = do
                     pi <- subIfVar pi'
                     return (Value pi)
reduce (CaseDecrypt encrypted' var key' piproc) = do
                                                   --liftIO $ putStrLn (show (CaseDecrypt encrypted' var key'
                                                   encrypted <- subIfVar encrypted'
                                                   key <- subIfVar key'
                                                   case encrypted of
                                                    (Encryption mess keyin) -> if keyin == key then do
                                                        (MyState gam tvar ls mv) <- get
                                                        let gam' = (VarBind (var, mess)): gam 
                                                        put (MyState gam' tvar ls mv) -- update the state to have this variable
                                                        reduce piproc
                                                         else return Stuck
                                                    (_) -> return Stuck

waitForFresh :: (MVar (Pi,Int)) ->Int -> MyStateTMonad (Pi,Int)
waitForFresh mvarP counter = do
                        x@(mess,i) <- liftIO $ takeMVar mvarP
                        (MyState gam glob ls m) <- get
                        if elem i ls then do 
                                            liftIO $ tryPutMVar mvarP x
                                            liftIO yield --a little nudge in the right direction
                                            if counter> 1000000 then error "looping forever waiting for new message"
                                                                else waitForFresh mvarP (counter +1)
                                     else do 
                                             liftIO $ tryPutMVar mvarP x 
                                             return x 
getMessageID :: MyStateTMonad Int
getMessageID = do
                (MyState g tvar idLS mvidP) <- get
                mvid <- liftIO $ takeMVar mvidP
                liftIO $ putMVar mvidP (mvid + 1)
                return mvid
                
isPresent ::  Pi -> [(Pi,MVar (Pi,Int))] -> Bool
isPresent _ []  = False
isPresent t (x:xs) = if t == (fst x) then True else isPresent t xs

findMVar ::  Pi -> [(Pi,MVar (Pi,Int))] -> Maybe (MVar (Pi,Int)) 
findMVar pi1 [] = Nothing
findMVar pi1 (x:xs) = if pi1 == (fst x) then Just (snd x)
                                        else findMVar pi1 xs
                                                    
subIfVar :: Pi -> MyStateTMonad Pi
subIfVar pi = do
               s<- get
               --put s
               --let gamma = x --fst s
               return $ subIfVar' pi (gamma s) 
               -- case myLookup pi (gamma s) of
                    -- Nothing -> return pi
                    -- Just val -> return val
subIfVar' :: Pi -> Gamma -> Pi
subIfVar' (Pair x y) gam = Pair (subIfVar' x gam) (subIfVar' y gam) --added this. def needed.
subIfVar' (Encryption pi1 pi2) gam = Encryption (subIfVar' pi1 gam) (subIfVar' pi2 gam) -- added this. def needed as well.
subIfVar' pi gamma = case myLookup pi gamma of
                      Nothing -> pi
                      Just val -> val
                    
myLookup :: Pi -> Gamma -> Maybe Pi
myLookup pi []     = Nothing
myLookup pi (t:xs) = case t of
                          VarBind (x,y) -> if x == pi then return y else myLookup pi xs 
                          _ -> myLookup pi xs                                                    


fst3 :: (a,b,c) -> a 
fst3 (a,_,_) = a
snd3 :: (a,b,c) -> b 
snd3 (_,b,_) = b                           
thd :: (a,b,c) -> c
thd (_,_,c) = c
                          

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
                       gammaR       :: Gamma,
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
                                            let gamgam = gamma (snd x)
                                            return (Right (Result (fst x) gamgam t))
                      
runReduceShow term= do
                      putStrLn "BEGINNING REDUCTION"                    
                      x <- runReduce term
                      putStrLn "RESULT:"
                      print (fst x)
                      s <- atomically $ readTMVar (globalChans (snd x))
                      let gam = gamma (snd x)
                      putStrLn ("Gamma: " ++ (show gam))
                      putStrLn "END SUCCESSFUL REDUCTION"



                          

              
              
              