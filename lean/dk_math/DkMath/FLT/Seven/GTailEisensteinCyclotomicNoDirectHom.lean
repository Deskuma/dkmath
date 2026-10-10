/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailGlobalBalanceFirewall

#print "file: DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory
open SevenCyclotomicDegreeSixInt

/-- A genuine nontrivial seventh root supplies the degree-six residue evaluation. -/
theorem seven_root_zmod29 : (7 : ZMod 29) ≠ 0 ∧ (7 : ZMod 29) ^ 7 = 1 ∧
    (7 : ZMod 29) ≠ 1 := by decide

/-- The Eisenstein generator relation has no image in characteristic twenty-nine. -/
theorem no_eisenstein_root_zmod29 (x : ZMod 29) : x ^ 2 - x + 1 ≠ 0 := by
  have h : ∀ y : ZMod 29, y ^ 2 - y + 1 ≠ 0 := by decide
  exact h x

/-- An actual Eisenstein residue root in characteristic thirteen. -/
theorem eisenstein_root_zmod13 : (4 : ZMod 13) ^ 2 - 4 + 1 = 0 := by decide

/-- The complete seventh cyclotomic relation has no image in characteristic thirteen. -/
theorem no_seven_geom_root_zmod13 (x : ZMod 13) :
    1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 ≠ 0 := by
  have h : ∀ y : ZMod 13, 1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 ≠ 0 := by decide
  exact h x

private theorem eisenstein_tau_relation : (tau (-1)) ^ 2 - tau (-1) + 1 = 0 := by
  rw [pow_two, traceOne_tau_sq]
  ext <;> norm_num [ofInt, tau]

/-- No direct unital ring map from the actual Eisenstein order to the degree-six order. -/
theorem not_nonempty_eisenstein_to_seven_cyclotomic :
    ¬ Nonempty (TraceOneInt (-1) →+* SevenCyclotomicDegreeSixInt.Ring) := by
  rintro ⟨f⟩
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  let ev := evalCyclotomicFromSeventhRoot (7 : ZMod 29)
    seven_root_zmod29.1 seven_root_zmod29.2.1 seven_root_zmod29.2.2
  let h := ev.comp f
  have hx : (h (tau (-1))) ^ 2 - h (tau (-1)) + 1 = 0 := by
    simpa only [map_pow, map_sub, map_add, map_one, map_zero] using
      congrArg h eisenstein_tau_relation
  exact no_eisenstein_root_zmod29 _ hx

/-- No direct unital ring map in the reverse direction, using the complete ζ relation. -/
theorem not_nonempty_seven_cyclotomic_to_eisenstein :
    ¬ Nonempty (SevenCyclotomicDegreeSixInt.Ring →+* TraceOneInt (-1)) := by
  rintro ⟨f⟩
  let ev := eisensteinResidueRingHom (4 : ZMod 13) eisenstein_root_zmod13
  let h := ev.comp f
  have hx : 1 + h zeta + h zeta ^ 2 + h zeta ^ 3 + h zeta ^ 4 + h zeta ^ 5 + h zeta ^ 6 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg h zeta_geom_sum
  exact no_seven_geom_root_zmod13 _ hx

end DkMath.FLT.Seven
