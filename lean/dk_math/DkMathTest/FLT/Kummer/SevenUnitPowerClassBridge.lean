/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenUnitPowerClassBridge
import DkMath.NumberTheory.GapFocusing.UnitGauge

#print "file: DkMathTest.FLT.Kummer.SevenUnitPowerClassBridge"

namespace DkMathTest.FLT.Kummer.SevenUnitPowerClassBridge

open DkMath.Lib.Algebra DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm

-- A nontrivial root correction, keeping the same t for roots and units.
example : ∃ t : ℤˣ, (-3 : ℤ) = (t : ℤ) * 3 ∧ (1 : ℤˣ) = (-1 : ℤˣ) * t ^ 7 := by
  exact exists_root_and_unit_correction (-1 : ℤˣ) 1 (by decide : 7 ≠ 0)
    (by decide : (2 * 3 ^ 7 : ℤ) ≠ 0) (by decide : (2 : ℤ) ≠ 0)
    (by norm_num) (by norm_num)

example : ((-1 : ℤˣ) : ℤˣ ⧸ unitPowerSubgroup ℤ 7) = (1 : ℤˣ ⧸ unitPowerSubgroup ℤ 7) := by
  apply sameUnitPowerClass_iff_quotient_eq.mp
  exact ⟨-1, by decide⟩

example : ∃ k : ℤˣ, (-1 : ℤˣ) = k ^ 7 := by
  exact exists_unit_pow_of_fixed_extraction (beta := (-3 : ℤ)) (gamma := 3) (-1 : ℤˣ) 1 (by decide : 7 ≠ 0)
    (by decide : (2 * 3 ^ 7 : ℤ) ≠ 0) (by decide : (2 : ℤ) ≠ 0)
    (by norm_num) (by norm_num) ⟨1, by simp⟩

-- A nontrivial ramifier twist cannot be dropped, even in a field (hence Dedekind domain).
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
private def w : (ZMod 29)ˣ := ⟨2, 15, by decide, by decide⟩

private theorem w_nontrivial : ¬ SameUnitPowerClass 7 w 1 := by
  change ¬ ∃ t : (ZMod 29)ˣ, w = 1 * t ^ 7
  decide +kernel

example : ¬ SameUnitPowerClass 7 w 1 := w_nontrivial

example : (w : ZMod 29) = 1 * ((w : ZMod 29) * (1 : ZMod 29) ^ 7) ∧
    (w : ZMod 29) = ((w : ZMod 29) * 1) * ((1 : ZMod 29) * (1 : ZMod 29) ^ 7) := by simp

-- At A=0 any unit works, so equality of decompositions no longer determines its class.
example : (0 : ZMod 29) = 1 * ((w : ZMod 29) * (0 : ZMod 29) ^ 7) ∧
    (0 : ZMod 29) = 1 * ((1 : ZMod 29) * (0 : ZMod 29) ^ 7) ∧
    ¬ SameUnitPowerClass 7 w 1 := by
  refine ⟨by simp, by simp, ?_⟩
  exact w_nontrivial

-- Research names remain usable after promoting the neutral API into Lib.
example : DkMath.NumberTheory.GapFocusing.SameUnitPowerClass 7 (-1 : ℤˣ) 1 :=
  ⟨-1, by decide⟩

example (hi : 1 ∈ (Finset.range 7).erase 0) :
    ∃ k : SevenCyclotomicDegreeSixInt.Ringˣ, GNRamifierTwist hi = k ^ 7 := by
  refine ⟨-1, ?_⟩
  rw [GNRamifierTwist_one]
  norm_num

-- The actual cyclotomic correction at phase 2 has nontrivial seventh-power class.
example (hi : 2 ∈ (Finset.range 7).erase 0) :
    (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ringˣ ⧸
      unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).mp h
  exact GNRamifierTwist_two_not_seventh hi ⟨k, hk.symm⟩

#print axioms exists_root_and_unit_correction
#print axioms quotient_eq_of_fixed_extraction
#print axioms GNRamifierTwist_two_not_seventh
#print axioms currentCarrier_unit_class_of_GN_source

run_cmd do
  for n in #[
      ``DkMath.Lib.Algebra.SameUnitPowerClass,
      ``DkMath.Lib.Algebra.unitPowerClass_independent,
      ``DkMath.Lib.Algebra.fixedRamifier_unitPowerClass_independent,
      ``DkMath.Lib.Algebra.sameUnitPowerClass_of_fixed_extraction,
      ``DkMath.Lib.Algebra.sameUnitPowerClass_iff_quotient_eq,
      ``DkMath.Lib.Algebra.exists_unit_pow_of_same_class,
      ``DkMath.Lib.Algebra.quotient_eq_of_fixed_extraction,
      ``DkMath.Lib.Algebra.exists_root_and_unit_correction,
      ``DkMath.Lib.Algebra.exists_unit_pow_of_fixed_extraction,
      ``DkMath.Lib.Algebra.sameUnitPowerClass_of_rescaled_extraction,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNPhaseFactor,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist_spec,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNPhaseFactor_decomposition,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.unit_class_of_GN_source,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.unit_seventh_after_twist_of_GN_source,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist_one,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist_two_norm,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.GNRamifierTwist_two_not_seventh,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.unit_seventh_of_GN_source,
      ``DkMath.FLT.Kummer.SevenPrimaryNorm.currentCarrier_unit_class_of_GN_source] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.SevenUnitPowerClassBridge
