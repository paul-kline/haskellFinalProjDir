--pi calculus language
module ISpi where


data Pi = Name String
	| Pair Pi Pi
	| Zero
	| Succ Pi
        | Var String deriving (Show, Eq)
data PiProcess = Output Pi Pi PiProcess
               | Input Pi (Pi) PiProcess --Input Pi (Var String) PiProcess
               | Composition PiProcess PiProcess
               | Restriction (Pi) PiProcess --Restriction (Name String) PiProcess
               | Replication PiProcess
               | Match Pi Pi PiProcess
               | Nil
               | Let (Pi,Pi) Pi PiProcess
               | Case Pi Pi PiProcess Pi PiProcess deriving (Show, Eq)
               
        
        
        
        
        
--Pi type checker
data PiType = TPiNumber 
       | TPiNonNumber 
       | TPair PiType PiType deriving (Show, Eq)



typeCheckPi :: Pi -> Either String PiType
typeCheckPi (Name str) = Right TPiNonNumber
typeCheckPi (Pair a b) = case typeCheckPi a of
                                Left str -> Left ("First of Pair type fail: " ++ str) 
                                Right fstT -> case typeCheckPi b of
                                                Left str -> Left ("Second member of Pair type fail: " ++ str)
                                                Right sndT ->  Right (TPair fstT sndT)                                
typeCheckPi Zero = Right TPiNumber
typeCheckPi x@(Succ t) = case typeCheckPi t of
                              Left str -> Left (str) --no extra error text here to prevent recursive error message. 
                              Right TPiNumber -> Right TPiNumber
                              Right _ -> Left ("Succ of non-numberic type: " ++ (show x))
typeCheckPi (Var _) = Right TPiNonNumber                              
typeCheckPi x = Left ("Type failure: " ++ (show x))

testPiGood = Pair (Succ (Succ (Succ Zero))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
testPi1Bad = Pair (Succ (Succ (Succ (Var "varhere1")))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
testPi2Bad = Pair (Succ (Succ (Succ (Zero)))) (Pair (Name "namehere") (Pair Zero (Var "varhere")))
