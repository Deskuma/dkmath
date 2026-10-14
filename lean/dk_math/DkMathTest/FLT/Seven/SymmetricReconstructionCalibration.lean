/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSymmetricReconstruction

#print "file: DkMathTest.FLT.Seven.SymmetricReconstructionCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven DkMath.CosmicFormulaBinom
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Exercise the signed expansion in a case with a negative higher term. -/
theorem alternating_value : alternatingCyclotomicSeven 3 4 = 2653 := by
  norm_num [alternatingCyclotomicSeven]

theorem normalized_alternating_value : alternatingCyclotomicSeven 3 4 / 7 = 379 := by
  rw [alternating_value]

/-- Full modulus seven is stronger than the trivial sum/7 modulus one. -/
theorem normalized_full_sum : Nat.ModEq 7 379 (4 ^ 6) := by decide

theorem normalized_sum_fourteen :
    Nat.ModEq 14 (alternatingCyclotomicSeven 3 11 / 7) (11 ^ 6) :=
  alternatingCyclotomicSeven_div_seven_modEq_sum 3 11 (by decide)

/-- Retain the totalized zero-sum boundary of natural division. -/
theorem normalized_zero_sum :
    Nat.ModEq 0 (alternatingCyclotomicSeven 0 0 / 7) (0 ^ 6) :=
  alternatingCyclotomicSeven_div_seven_modEq_sum 0 0 (dvd_zero 7)

theorem endpoint_exchange :
    alternatingCyclotomicSeven 4 3 = alternatingCyclotomicSeven 3 4 :=
  alternatingCyclotomicSeven_comm 4 3

/-- The common helper is available without either outer factor packet. -/
theorem common_allocation :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      343 = 7 ^ 3 * r ^ 7 ∧ 1 = s ^ 7 ∧ 1 = r * s :=
  exists_nested_seventh_allocation (by decide) (by decide) (by decide) (by decide)
    (by norm_num)

/-- Coprimality with the sum transports to primitive endpoint coprimality. -/
theorem primitive_endpoint_bridge {D u : ℕ} (hu : u < D) :
    Nat.Coprime u (D - u) ↔ Nat.Coprime u D :=
  Nat.coprime_sub_self_right hu.le

theorem zero_core_receiver_absent : ¬ NestedRightHandSideCondition 0 := by
  rintro ⟨r, s, _, hr, hs, _, _, hM, _⟩
  have : 0 < r * s := Nat.mul_pos hr hs
  omega

theorem zero_core_chart_absent :
    ¬ ∃ u v : ℕ, CounterexamplePack u v (7 ^ 4 * 0 ^ 7) := by
  rw [rightHandSideChart_iff_nested]
  exact zero_core_receiver_absent

theorem right_chart_equivalence (M : ℕ) :
    (∃ u v : ℕ, CounterexamplePack u v (7 ^ 4 * M ^ 7)) ↔
      NestedRightHandSideCondition M := rightHandSideChart_iff_nested M

theorem nested_normalized_congruence {r s u v : ℕ}
    (hsum : u + v = 7 ^ 27 * r ^ 49)
    (hAlt : alternatingCyclotomicSeven u v = 7 * s ^ 49) :
    Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (v ^ 6) :=
  (nestedAlternatingResidual_full_sum_congruence hsum hAlt).2

/-- The second branch remains present, now in the same scalar currency. -/
theorem matched_reconstruction_disjunction (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      NestedPrescribedSummandCondition (internalDepthFourSeventhCore p) ∨
        NestedRightHandSideCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_two_nested_receivers p

end DkMathTest.FLT.Seven
