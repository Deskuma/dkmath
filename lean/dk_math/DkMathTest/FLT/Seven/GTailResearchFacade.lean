/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTail

#print "file: DkMathTest.FLT.Seven.GTailResearchFacade"

/-!
# GTail research facade smoke and axiom check

All declarations are reached through the dedicated research facade only.
These are previously proved, in several cases explicitly conditional, APIs.
No positive Fermat7 counterexample or unconditional FLT7 closure is asserted.
-/

#check DkMath.FLT.Seven.gtail_seven_shell
#check DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance
#check DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein
#check DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic
#check DkMath.FLT.Seven.GTailPrimeGrid.M_injective
#check DkMath.FLT.Seven.GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic
#check DkMath.FLT.Seven.GTailGenericPrimeReceiver.nativeKernel
#check DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_prime_route
#check DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate
#check DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size
#check DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_size_without_full_support

#print axioms DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance
#print axioms DkMath.FLT.Seven.GTailPrimeJoin.M_eq_map_eisenstein_sup_map_cyclotomic
#print axioms DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate
#print axioms DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size
