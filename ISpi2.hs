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
                                     mv1 <- liftIO $ newEmptyMVar --To ensure we finish before continuing.
                                     mv2 <- liftIO $ newEmptyMVar -- ''
                                     s <- get
                                     liftIO $ do                                                  
                                                  forkIO $ do
                                                         p1 <-runStateT (reduce proc1) s
                                                         print ((show (fst p1)) !! 0)
                                                         putMVar mv1 p1
                                                         
                                                  forkIO $ do
                                                         p2 <-runStateT (reduce proc2) s
                                                         print ((show (fst p2)) !! 0)
                                                         putMVar mv2 p2
                                                         
                                     res1 <- liftIO $ takeMVar mv1
                                     res2 <- liftIO $ takeMVar mv2
                                     (MyState x y ls m) <- get
                                     let res1gamma = gamma (snd res1)
                                     let res2gamma = gamma (snd res2)
                                     put (MyState (union res1gamma res2gamma) y ls m)   --currently just for compatibility with Adam's stuff.
                                     return (Composition (fst res1) (fst res2))         --return the result of reducing the two.
reduce (Output pi1' pi2' piproc)   = do
                                      (MyState _ tmvar _  _) <- get
                                      tmvarContents <- liftIO $ atomically $ takeTMVar tmvar -- ----------------------------------------------------------LOCK TMVar
                                      pi1 <- subIfVar pi1'
                                      pi2 <- subIfVar pi2'
                                      liftIO $ putStrLn ("OUT:" ++ (show (Output pi1 pi2 piproc)))
                                      (MyState gam tmvarx ls m) <- get                    --the thinking here is that between getting the state and 
                                      --tmvarContents :: [(Pi,MVar Pi,Int)]               --locking on the TMVar, the state may have changed. So now that
                                                                                          --we have the lock, let's get the state. (mainly the current ID state (m) may have changed.)
                                                                                          -- I believe that counter is only changed inside the lock of the TMVar. Let me check. yeah only called in this method while locked.
                                      case findMVar pi1 tmvarContents of
                                        Nothing -> do --No one is yet blocking on this mvar because it doesn't exist yet.
                                                    mID <- getMessageID --compute a unique message identifier.
                                                    liftIO $ putStrLn ("new mess ID:" ++ (show mID)) --force the messageID computation. No thunk crap.
                                                    mvr <-liftIO $ newMVar (pi2,mID)
                                                    let tmvarContents' = (pi1,mvr):tmvarContents --the new TMVARcontents contains the new channel-message information.
                                                    if canReadOwn then do --if we allow ourselves to read our own messages, no action is needed here.
                                                                        return ()
                                                                  else do -- we are disallowing reading own messages, add current messageID to no-no list. 
                                                                            (MyState gam' tmvar' lsOld m') <- get --state gotten again for out of fear. shouldn't make a difference if uneccessary.  
                                                                            let ls' = mID:lsOld                                                                            
                                                                            put (MyState gam' tmvar' ls' m')
                                                    liftIO $ atomically $ putTMVar tmvar tmvarContents' 
                                        Just pimvar -> do --This channel exists. Someone could be waiting for a message. 
                                                        maybemvrC <- liftIO $ tryTakeMVar pimvar --leaves the MVar empty no matter what. don't care about the result.
                                                        replacementID <- getMessageID
                                                        liftIO $ putStrLn ("ID:" ++ (show replacementID)) -- must be here. force computation.
                                                        liftIO $ putMVar pimvar (pi2, replacementID)
                                                        if canReadOwn then do --put (MyState gam tmvar ls m) --added idk why. only diff I see.
                                                                              return ()
                                                                      else do
                                                                            (MyState gam' tmvar' lsOld m') <- get
                                                                            let ls' = replacementID:lsOld                                                                            
                                                                            put (MyState gam' tmvar' ls' m')
                                                        liftIO $ atomically $ putTMVar tmvar tmvarContents
                                                                                                             -- -----------------------------------------------RELEASE TMVar
                                      --at this point we have put the message out there and can continue
                                      reduce piproc
reduce (OrderedOutput _ from to pi piproc) = reduce (Output (Name ("C_" ++ (if from < to then (from ++ to) else (to ++ from)))) pi piproc)
reduce (Input pi1' pi2 piproc)   = do
                                    (MyState _ tmvarP _ _) <- get
                                    tmvarC <- liftIO $ atomically $ takeTMVar tmvarP  -- ---------------------------------------------------------------------LOCK TMVar
                                    pi1 <- subIfVar pi1'
                                    (MyState gam tmvarPx ls m) <- get --don't get the state until we have a lock (m could have changed).
                                    
                                  --tmvarC :: [(Pi,MVar Pi)]
                                    liftIO $ putStrLn ("IN:" ++ (show (Input pi1 pi2 piproc))) --just to see. not necessary like other prints.
                                    case findMVar pi1 tmvarC of
                                        Nothing -> do --the MVar containing the message we are looking for doesn't exist yet. we create it, release the TMVAr so
                                                      --another thread can edit. This way we are guranteed to at least have an empty MVar to block on here in a sec.
                                                    mvr <-liftIO $ newEmptyMVar
                                                    let tmvarContents' = (pi1,mvr):tmvarC
                                                    liftIO $ atomically $ putTMVar tmvarP tmvarContents'
                                                    liftIO $ yield
                                        Just mvr -> do
                                                        liftIO $ atomically $ putTMVar tmvarP tmvarC
                                    --whether or not I had to put an emptyMVar there, it's there and TMVAR can be taken -------------------------------------RELEASE TMVar
                                    tmvarC' <- liftIO $ atomically $ readTMVar tmvarP --non blocking
                                    case findMVar pi1 tmvarC' of
                                        Nothing     -> liftIO $ putStrLn "This should never happen ever. ever ever." --like for real, we guaranteed this can't happen in the previous case statement.
                                        Just pimvar -> do 
                                                        inputMessage <- if (and [canReReceive, canReadOwn]) then liftIO $ takeMVar pimvar --only if we can canReReceive and canReadOwn do we not care about fresh messages.
                                                                                                            else waitForFresh pimvar 0    --otherwise there exists some messages we wish to ignore. 
                                                        --inputMessage <-liftIO $ takeMVar pimvar
                                                        (MyState gam_ tmvP ls_ m_) <- get
                                                        let ls' = if canReReceive then ls
                                                                                  else (snd inputMessage) : ls_
                                                        let piMess = fst inputMessage
                                                        
                                                        let gam' = (VarBind (pi2, piMess)):gam_
                                                        put (MyState gam' tmvP ls' m_)
                                                        if canBroadcast then do liftIO $ tryPutMVar pimvar inputMessage --try because it might have been put back by waitForFresh
                                                                                return ()
                                                                        else do liftIO $ tryTakeMVar pimvar --try because waitForFresh always puts it back.
                                                                                return ()
                                                        
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
                put (MyState g tvar idLS mvidP)
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
                      --putStrLn ("Gamma: " ++ (show gam))
                      putStrLn "END SUCCESSFUL REDUCTION"



                          

              
              
              