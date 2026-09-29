import NormalNumbers.JointLambertPrimeInputs
open NormalNumbers.JointLambert
example : PrimeIntervalSupply := primeIntervalSupply_holds
example : AGP → JointLambertDisjunctivity := jointLambertDisjunctivity_of_agp
example : AGP → JointWords ({2,4} : Finset Nat) := jointWords_two_four_of_agp
#print axioms NormalNumbers.JointLambert.primeIntervalSupply_holds
#print axioms NormalNumbers.JointLambert.jointLambertDisjunctivity_of_agp
#print axioms NormalNumbers.JointLambert.jointWords_two_four_of_agp
