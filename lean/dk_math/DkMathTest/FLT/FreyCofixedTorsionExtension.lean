/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedTorsionExtension
import DkMath.FLT.FreyTorsionInertiaAbsorption

namespace DkMathTest.FLT.FreyCofixedTorsionExtension

open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

#check residual_cofixed_preimage_extension_profile
#check residual_cofixed_preimage_quotient_cyclotomic
#check residual_preimage_stable_complement_lifts
#check residual_line_tower_inertia_frobenius_impossible

#print axioms preimageRepresentation_kernel_isOpen
#print axioms card_preimageQuotient
#print axioms finrank_preimageQuotient
#print axioms card_torsionImage_of_cyclic
#print axioms finrank_torsionImage_of_cyclic
#print axioms exists_tower_step_of_stable_complement
#print axioms DkMath.Lib.Algebra.PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent
#print axioms residual_cofixed_preimage_extension_profile
#print axioms residual_cofixed_preimage_quotient_cyclotomic
#print axioms residual_preimage_stable_complement_lifts
#print axioms prime_power_pointAction_sub_mem_of_bad_inertia
#print axioms residual_line_tower_inertia_frobenius_impossible

end DkMathTest.FLT.FreyCofixedTorsionExtension
