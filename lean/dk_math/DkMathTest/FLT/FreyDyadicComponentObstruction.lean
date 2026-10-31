/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyDyadicComponentObstruction

#print "file: DkMathTest.FLT.FreyDyadicComponentObstruction"

namespace DkMathTest.FLT.FreyDyadicComponentObstruction

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source

#check residualDyadicValuationModel
#check residualDyadicValuationModel_map_subtype
#check residualDyadicValuationModel_residue_invariants
#check residual_cofixed_forces_dyadic_component_prime_dvd
#check residual_cofixed_forces_dyadic_component_prime_order

#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_dyadic_component_prime_dvd
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_dyadic_component_prime_order

end DkMathTest.FLT.FreyDyadicComponentObstruction
