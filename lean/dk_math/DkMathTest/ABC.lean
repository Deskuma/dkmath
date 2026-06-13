import DkMath.NumberTheory.ValuationFlow.Primitive
import DkMath.ABC.ChernoffMgf
import DkMath.ABC.ValuationFlowBridge

#print "file: DkMathTest.ABC"

namespace DkMath.ABC
open DkMath.NumberTheory

#check mgf_padic_excess_bound_pbase


-- OK: all no-sorry 2026/06/13 20:47
-- DkMath.NumberTheory
#print axioms ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_noLift_beam
#print axioms ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
-- DkMath.ABC
#print axioms mgf_padic_excess_bound_pbase
#print axioms noLift_beam_bounds_local_load
#print axioms squarefree_beam_bounds_local_load_local

end DkMath.ABC
