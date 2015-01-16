{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
--pi calculus language
module SpiExamples where


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

import SpiTypes




	  
examplePiVALID = Pair (Succ (Succ (Succ Zero))) 
                (Pair (Name "namehere") 
                (Pair Zero (Var "varhere")))
                
--demonstrates succ (Variable) is valid.                
examplePiVALIDSuccVar = Pair (Succ (Succ (Succ (Var "varhere1")))) 
                       (Pair (Name "namehere") 
                       (Pair Zero (Var "varhere")))
                       
-- demonstrates succ (non-number , non-variable) invalid                       
examplePiINVALIDSucc = Pair (Succ (Succ (Succ (Name "name")))) 
                      (Pair (Name "namehere") 
                      (Pair Zero (Name "varhere")))

--tries to output a channel that is NOT a name.                                  
piprocINVALIDOutoutToNonChan = Output Zero Zero 
                               Nil   
piprocVALIDOutput            = Output (Name "channel") (Name "message") 
                               Nil
piprocVALIDInput             = Input (Name "channel") (Name "message") 
                               Nil
piprocVALIDComposition = Composition piprocVALIDOutput piprocVALIDInput
piprocINVALIDChain = Chain [ piprocINVALIDOutoutToNonChan, 
                             a_m231, 
                             a_m231,
                             piprocINVALIDOutoutToNonChan, 
                             b231]
piprocVALIDRestriction = Restriction (Var "varname") 
                        (Restriction (Var "varname2") 
                         Nil)
                         
--demonstrates proper Case reducing                         
piprocVALIDCase = Case Zero 
                    (Succ Zero) 
                      (Value (Name "Shouldn't get here")) 
                    Zero 
                      (Value (Name "Should get here"))  
piprocVALIDCaseWVariable   = Case Zero 
                       (Var "variablename") 
                          (Value (Name "Shouldn't get here")) 
                        Zero 
                          (Value (Name "Should get here"))
piprocINVALIDCaseNonNumber = Case (Name "num should be here or Var") 
                        Zero 
                          (Value (Name "Shouldn't get here")) 
                        (Succ Zero) 
                          (Value (Name "Shouldn't get here")) 
piprocINVALIDCaseStuck     = Case Zero 
                        (Succ Zero) 
                          (Value (Name "Shouldn't get here")) 
                        (Succ Zero) 
                          (Value (Name "Shouldn't get here")) 
                                                                                                                                                                                       
-- PiProc example 2.3.1
a_m231 = Output (Name "C_ab") Zero 
         Nil --A(M) sends zero on channel AB
b231   = Input (Name "C_ab") (Var "x") 
        (Restriction (Var "x") 
         Nil)
inst_m231 = Restriction (Name "C_ab") 
           (Composition a_m231 b231)
inst_m231' = Restriction (Name "C_ab") 
            (Composition b231 a_m231)

a_m231BADChan = Output (Name "C_az") Zero 
                Nil --A(M) sends zero on channel AB
b231BADChan   = Input (Name "C_ab") (Var "x") 
               (Restriction (Var "x") 
                Nil)
inst_m231BADChan = Restriction (Name "C_ab") 
                  (Composition a_m231BADChan b231BADChan)
 
						  
--page 13 example protocol
a_m2 = Restriction (Name "C_ab") 
      (Output (Name "C_as") (Name "C_ab") 
      (Output (Name "C_ab") (Name "Message from a to b should be here") 
       Nil))
s    = Input (Name "C_as") (Var "x") 
      (Output (Name "C_sb") (Var "x") 
       Nil)
b2   = Input (Name "C_sb") (Var "x") 
      (Input (Var "x") (Var "messageFromA") 
       Nil) --(Input (Var "xb") (Var "messageFromA") Nil)
inst_m2 = Restriction (Name "C_as") 
         (Restriction (Name "C_sb") 
         (Composition a_m2 
         (Composition s b2)))
         
-- this is same as above page 13 example proto, 
-- but shows the value received at the end.
a_m2'    = Restriction (Name "C_ab") 
          (Output (Name "C_as") (Name "C_ab") 
          (Output (Name "C_ab") (Name "Message from a to b should be here") 
           Nil))
s'       = Input (Name "C_as") (Var "x") 
          (Output (Name "C_sb") (Var "x") 
          (Value (Var "x")))
b2'      = Input (Name "C_sb") (Var "x") 
          (Input (Var "x") (Var "messageFromA") 
          (Value (Var "messageFromA"))) --(Input (Var "xb") (Var "messageFromA") Nil)
inst_m2' = Restriction (Name "C_as") 
          (Restriction (Name "C_sb") 
          (Composition a_m2' 
          (Composition s' b2')))


--our protocol
--appraiser
armored_a = OrderedOutput 1 "a" "b" (Name "InitRequestTOAttester") 
           (Input (Name "C_ab") (Var "fromAtt1") 
           (Input (Name "C_ab") (Var "fromAtt2") 
           (Value (Pair (Var "fromAtt1") (Var "fromAtt2")))))
--attester
armored_b = Input (Name "C_ab") (Var "ReqFromApp") 
           (OrderedOutput 2 "b" "c" (Name "b + AIK") 
           (Input (Name "C_bc") (Var "caCert")
           (CaseDecrypt (Var "caCert") (Var "decryptedcaCert") (Name "BSECRETKEY")
           (OrderedOutput 4 "b" "m" (Name "pleasegiveMeas1") 
           (Input (Name "C_bm") (Var "measurementFromMeas") 
           (OrderedOutput 6 "b" "a" (Var "decryptedcaCert") 
           (OrderedOutput 7 "b" "a" (Var "measurementFromMeas") 
           (Value (Pair (Var "ReqFromApp") 
                  (Pair (Var "decryptedcaCert") (Var "measurementFromMeas"))
                  ))
           )))))))
armored_c = Input (Name "C_bc") (Var "reqToCA")
           (OrderedOutput 3 "c" "b" 
           (Encryption (Name "CA Cert (Encrypted!)") (Name "BSECRETKEY")) 
           (Value (Var "reqToCA")))
armored_m = Input (Name "C_bm") (Var "desE")
           (OrderedOutput 5 "m" "b" (Name "pretend this is evidence") 
           (Value (Var "desE")))
inst_armored =Restriction (Name "C_bm")
             (Restriction (Name "C_ab")
             (Composition armored_a 
             (Composition armored_b 
             (Composition armored_c armored_m))))
              
              
              
examplewhyBroken_a = Output (Name "C_ab") (Name "Hello") 
                    (Input (Name "C_ab") (Var "x") (Value (Var "x"))) 
                    
examplewhyBroken_b = Let ((Var "1"),(Var "2")) 
                        (Pair (Name "name1") (Name "name2"))
                    (Let ((Var "1"),(Var "2")) 
                        (Pair (Name "name1") (Name "name2"))
                    (Let ((Var "1"),(Var "2")) 
                        (Pair (Name "name1") (Name "name2"))
                    (Let ((Var "1"),(Var "2")) 
                        (Pair (Name "name1") (Name "name2")) 
                    (Let ((Var "1"),(Var "2")) 
                        (Pair (Name "name1") (Name "name2")) 
                    (Input (Name "C_ab") (Var "x") 
                    (Output (Name "C_ab") (Pair (Var "x") (Var "x")) 
                     Nil))))))
inst_broken = Restriction (Name "C_ab") 
             (Composition examplewhyBroken_a examplewhyBroken_b)

examplewhyBroken_a' = Output (Name "C_ab") (Name "Hello") 
                     (Input (Name "C_ba") (Var "x") 
                     (Input (Name "C_ba") (Var "y")
                     (Value (Pair (Var "x") (Var "y"))))) 
                    
examplewhyBroken_b' = Input (Name "C_ab") (Var "x") 
                     (Output (Name "C_ba") (Name "poop")
                     (Output (Name "C_ba") (Name "Have a nice day Mr. A!")
                      Nil))
inst_broken' = Restriction (Name "C_ab") 
              (Composition examplewhyBroken_a' examplewhyBroken_b')


examplewhyBroken_af = Output (Name "C_ab") (Name "Hello") 
                     (Input (Name "C_ab") (Var "x") 
                     (Value (Var "x"))) 
                    
examplewhyBroken_bf = Input (Name "C_ab") (Var "x") 
                     (Output (Name "C_ab") (Pair (Var "x") (Var "x")) 
                      Nil)
inst_brokenf = Restriction (Name "C_ab") 
              (Composition examplewhyBroken_af examplewhyBroken_bf)

broadcast_asilly = Output (Name "C") (Name "Hello") 
                  (Input (Name "C") (Var "x") 
                  (Input (Name "C") (Var "y")
                  (Value (Pair (Var "x") (Var "y"))))) 
broadcast_bsilly = Input (Name "C") (Var "x") 
                  (Output (Name "C") (Pair (Name "B got:") (Var "x"))
                   Nil )
broadcast_csilly = Input (Name "C") (Var "x") 
                  (Output (Name "C") (Pair (Name "C got:") (Var "x")) 
                   Nil )
inst_broadcastsilly = Composition broadcast_asilly 
                     (Composition broadcast_bsilly broadcast_csilly)

broadcast_a = Output (Name "C") (Name "Hello") 
                    (Input (Name "C_ab") (Var "x") 
                    (Input (Name "C_ac") (Var "y")
                    (Value (Pair (Var "x") (Var "y"))))) 
broadcast_b = Input (Name "C") (Var "x") 
                    (Output (Name "C_ab") (Pair (Name "B got:") (Var "x")) 
                    (Value (Var "x")))
broadcast_c = Input (Name "C") (Var "x") 
                    (Output (Name "C_ac") (Pair (Name "C got:") (Var "x")) 
                    (Value (Var "x") ))
inst_broadcast = Composition broadcast_a 
                (Composition broadcast_b broadcast_c)

b_a = Output (Name "c") (Name "mess") 
      Nil
b_b = Input (Name "c") (Var "b") 
      Nil
b_c = Input (Name "c") (Var "c") 
      Nil
b_inst = Composition b_a 
        (Composition b_b b_c)