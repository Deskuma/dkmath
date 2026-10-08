/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionNestedReconstruction

#print "file: DkMathTest.FLT.Seven.NestedReconstructionCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven DkMath.CosmicFormulaBinom
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The full-gap modulus is nontrivial here, whereas d/7 would be one. -/
theorem normalized_seven_value : GN 7 (7 : ℕ) 1 / 7 = 42799 := by
  rw [GN_seven_div_seven_eq_head_add 7 1 (by decide)]
  norm_num

theorem normalized_seven_full_modulus : Nat.ModEq 7 42799 1 := by decide

/-- Retain the degenerate zero-gap boundary in the normalization theorem. -/
theorem normalized_zero_gap (u : ℕ) : GN 7 0 u / 7 = u ^ 6 := by
  rw [GN_seven_div_seven_eq_head_add 0 u (dvd_zero 7)]
  simp

/-- A partial allocation of the prime-power factor 4 fails coprimality. -/
theorem twelve_coprime_allocations :
    (12 : ℕ).divisors.filter (fun r => Nat.Coprime r (12 / r)) = {1, 3, 4, 12} := by decide

theorem fixed_gap_endpoint_unique {r s u v : ℕ}
    (hu : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49)
    (hv : GN 7 (7 ^ 27 * r ^ 49) v = 7 * s ^ 49) : u = v :=
  nestedResidual_unit_unique hu hv

theorem normalized_large_modulus {r s u : ℕ}
    (h : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (u ^ 6) :=
  nestedResidual_full_gap_congruence h

theorem factor_depths :
    padicValNat 7 (7 ^ 3 * 2 ^ 7) = 3 ∧
      padicValNat 7 (7 ^ 27 * 2 ^ 49) = 27 :=
  nestedFactor_exact_depths (by decide)

theorem summand_equivalence (M : ℕ) :
    (∃ u v : ℕ, CounterexamplePack u (7 ^ 4 * M ^ 7) v) ↔
      NestedPrescribedSummandCondition M :=
  prescribedSummandChart_iff_nested M

theorem divisor_receiver (M : ℕ) (hM : 0 < M) :
    NestedPrescribedSummandCondition M ↔
      ∃ r ∈ M.divisors, ∃ u : ℕ, 0 < u ∧ Nat.Coprime r (M / r) ∧
        Nat.Coprime u (7 * M) ∧ GN 7 (7 ^ 27 * r ^ 49) u = 7 * (M / r) ^ 49 :=
  nestedPrescribedSummandCondition_iff_divisor M hM

/-- The receiver must retain the independent right-hand-side chart branch. -/
theorem full_reconstruction_disjunction (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      NestedPrescribedSummandCondition (internalDepthFourSeventhCore p) ∨
        ∃ u v : ℕ, CounterexamplePack u v (internalDepthFourCarrier p) :=
  internalDepthFourReconstruction_iff_nested_or_left p

end DkMathTest.FLT.Seven
