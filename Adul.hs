module Adul where --ADam paUL

import qualified SpiTypes as I 
import SpiTypes
import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Identity

type Channel = String
type Entity = String
-- data Proto = Message Entity Entity String Channel
		   -- | Sequence Proto Proto
		   
-- type MyStateT a = StateT ([(String,I.PiProcess)], I.PiProcess) IO a	
	   
-- p12 = Sequence (Message "A" "B" "C_ab" "C_as") (Sequence (Message "S" "B" "C_ab" "C_sb") (Message "A" "B" "Message from A to B" "C_ab"))
		   
data Message = Message Int Entity Entity I.Pi deriving (Eq, Show)		   
toMessages :: I.PiProcess -> [Message] -> [Message]
toMessages (I.Composition proc1 proc2) messSoFar                   = toMessages proc1 (toMessages proc2 messSoFar)
toMessages (I.OrderedOutput int fromS toS pi2 piproc) messSoFar    = toMessages piproc ((Message int fromS toS pi2):messSoFar) 
toMessages (I.Input pi1 pi2 piproc) messSoFar                      = toMessages piproc messSoFar
toMessages (I.Restriction pi1 piproc) messSoFar  		           = toMessages piproc messSoFar
toMessages (I.Match pi1 pi2 piproc) messSoFar                      = toMessages piproc messSoFar
toMessages (I.Let (pi1, pi2) pi3 piproc) messSoFar 		           = toMessages piproc messSoFar
toMessages (I.Case pi0 pi1 piproc1 pi2 piproc2) messSoFar          = toMessages piproc1 (toMessages piproc2 messSoFar) -- this is very wrong since it's a conditional.
toMessages (I.Chain procs) messSoFar 					           = join (map (flip toMessages messSoFar) procs)    
toMessages (I.Value pi) messSoFar                                  = messSoFar                               
toMessages I.Nil messSoFar                                         = messSoFar  								 
toMessages (I.CaseDecrypt encrypted storeResVar keylimePi piProcess) messSoFar = toMessages piProcess messSoFar
		   
toRegularPi :: I.PiProcess -> I.PiProcess
toRegularPi (I.Composition proc1 proc2)                    = I.Composition (toRegularPi proc1) (toRegularPi proc2)
toRegularPi (I.OrderedOutput int fromS toS pi2 piproc)     = I.Output (I.Name ("C_" ++ (if fromS < toS then (fromS ++ toS) else (toS ++ fromS)))) pi2 (toRegularPi piproc)  --consistently ALWAYS alphabetical. Important note.
toRegularPi (I.Input pi1 pi2 piproc)                       = I.Input pi1 pi2 (toRegularPi piproc)
toRegularPi (I.Restriction pi1 piproc)   		           = I.Restriction pi1 (toRegularPi piproc)
toRegularPi (I.Match pi1 pi2 piproc)                       = I.Match pi1 pi2 (toRegularPi piproc)
toRegularPi (I.Let (pi1, pi2) pi3 piproc)  		           = I.Let (pi1, pi2) pi3 (toRegularPi piproc)
toRegularPi (I.Case pi0 pi1 piproc1 pi2 piproc2)           = I.Case pi0 pi1 (toRegularPi piproc1) pi2 (toRegularPi piproc2) -- this is very wrong since it's a conditional.
toRegularPi (I.Chain procs)  					           = case procs of
																	   []     -> I.Chain [I.Nil] 
																	   ls     -> I.Chain (map toRegularPi ls)
toRegularPi (I.Value pi)                                   = I.Value pi																	   
toRegularPi I.Nil                                          = I.Nil                                     		   



a_m2_shared    = Restriction (Name "C_ab") (OrderedOutput 1 "a" "s" (Name "C_ab") (OrderedOutput 3 "a" "b" (Name "Message from a to b should be here") Nil))
s_shared       = Input (Name "C_as") (Var "x") (OrderedOutput 2 "s" "b" (Var "x") (Value (Var "x")))
b2_shared      = Input (Name "C_bs") (Var "x") (Input (Var "x") (Var "messageFromA") (Value (Var "messageFromA"))) --(Input (Var "xb") (Var "messageFromA") Nil)
inst_m2_shared = Restriction (Name "C_as") (Restriction (Name "C_sb") (Composition a_m2_shared (Composition s_shared b2_shared)))

a_mSpi321 = OrderedOutput 1 "a" "b" (Encryption (Name "encrypted secret message!") (Name "SECRETabKEY")) Nil 
bSpi321   = Input (Name "C_ab") (Var "x") (CaseDecrypt (Var "x") (Var "res") (Name "SECRETabKEY") (Value (Var "res")))    
inst_mSPI321 = Restriction (Name "SECRETabKEY") (Composition a_mSpi321 bSpi321)

a_mSpi1WRONGKEY = OrderedOutput 1 "a" "b" (Encryption (Name "encrypted secret message!") (Name "SECRETabKEY")) Nil 
bSpi1WRONGKEY   = Input (Name "C_ab") (Var "x") (CaseDecrypt (Var "x") (Var "res") (Name "SECRETabKEYwrong") (Value (Var "res")))    
inst_mSPIWRONGKEY = Restriction (Name "SECRETabKEY") (Composition a_mSpi1WRONGKEY bSpi1WRONGKEY)