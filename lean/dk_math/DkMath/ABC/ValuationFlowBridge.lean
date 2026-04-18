/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.ValuationFlow.Primitive

#print "file: DkMath.ABC.ValuationFlowBridge"

namespace DkMath.ABC

open DkMath.NumberTheory.ValuationFlow

/-- Primitive primes contribute no boundary load. -/
theorem primitive_prime_gives_zero_boundary_load
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd1 : 1 < d) :
    boundaryMass q a b = 0 := by
  exact primitivePrimeFlow_boundaryMass_eq_zero hq hd1

/-- Primitive primes transfer all diff load to the beam factor. -/
theorem primitive_prime_transfers_diff_load_to_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    diffMass q a b d = beamMass q a b d := by
  exact primitivePrimeFlow_diffMass_eq_beamMass hq hd hd1 hab_lt

/--
Under a squarefree beam hypothesis, the local diff load is bounded by `1`.
-/
theorem squarefree_beam_bounds_local_load
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN d (a - b) b)) :
    diffMass q a b d ≤ 1 := by
  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq

end DkMath.ABC
