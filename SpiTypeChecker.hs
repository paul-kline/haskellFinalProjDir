module SpiTypeChecker where

import SpiTypes
import Control.Monad


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
            Right TVar -> case typeCheckPiProcess piProPrime of
               Left err     -> Left ("term 'Input' type fail on process subterm: " ++ err)
               Right primeT -> Right (TInput primeT)
            Right o    -> Left ("TYPE ERROR. Expected Var type for input, instead found: " ++ (show o))
      else Left ("Input on non-channel. Expected TName for channel. Actual type: " ++ (show tpi1))
typeCheckPiProcess (Output pi1 pi2 piProPrime) = case typeCheckPi pi1 of
      Left err   -> Left ("term 'Output' type fail on first pi argument: " ++ err)
      Right tpi1 -> if acceptablePi TName tpi1 then
         case typeCheckPi pi2 of
            Left err   -> Left ("term 'Output' type fail on second pi argument: " ++ err)
            Right tpi2 -> case typeCheckPiProcess piProPrime of
               Left err     -> Left ("term 'Output' type fail on process subterm: " ++ err)
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
typeCheckPiProcess (OrderedOutput _ from to pi piproc)   = typeCheckPiProcess (Output (Name ("C_" ++ (if from < to then (from ++ to) else (to ++ from)))) pi piproc)
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