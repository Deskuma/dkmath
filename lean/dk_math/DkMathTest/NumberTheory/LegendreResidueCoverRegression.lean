/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket
import DkMath.NumberTheory.Legendre.GnomonPrimorialTransition
import DkMathTest.NumberTheory.LegendreSqrtQuotientRegression

#print "file: DkMathTest.NumberTheory.LegendreResidueCoverRegression"

namespace DkMathTest.LegendreResidueCoverRegression
open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse
open DkMathTest.LegendreSqrtQuotientRegression DkMathTest.LegendreSqrtRoughCensusRegression
open scoped BigOperators
set_option maxRecDepth 100000

/-- Small periods and the prime/composite threshold transitions 4→5→6→7. -/
theorem small_periods :
    finitePrimeBasisProduct (primeScalesUpTo 1) = 1 ∧
    finitePrimeBasisProduct (primeScalesUpTo 2) = 2 ∧
    finitePrimeBasisProduct (primeScalesUpTo 3) = 6 ∧
    finitePrimeBasisProduct (primeScalesUpTo 4) = 6 ∧
    finitePrimeBasisProduct (primeScalesUpTo 5) = 30 ∧
    finitePrimeBasisProduct (primeScalesUpTo 6) = 30 ∧
    finitePrimeBasisProduct (primeScalesUpTo 7) = 210 := by
  decide +kernel

theorem small_collisions :
    squareShellWheelProjection (primeScalesUpTo 1) 1 1 =
      squareShellWheelProjection (primeScalesUpTo 1) 1 2 ∧
    squareShellWheelProjection (primeScalesUpTo 2) 2 1 =
      squareShellWheelProjection (primeScalesUpTo 2) 2 3 ∧
    squareShellWheelProjection (primeScalesUpTo 4) 4 1 =
      squareShellWheelProjection (primeScalesUpTo 4) 4 7 := by
  decide +kernel

theorem three_width_equal_period_injective :
    Set.InjOn (squareShellWheelProjection (primeScalesUpTo 3) 3) (squareOffsets 3) :=
  (squareShellWheelProjection_injOn_classification 3).mpr (Or.inr (Or.inl rfl))

theorem four_basis_and_image : primeScalesUpTo 4 = {2, 3} ∧
    squareShellWheelImage 4 = {0, 1, 2, 3, 4, 5} ∧
    escapingSquareOffsets 4 = {1, 3, 7} := by
  have hb : primeScalesUpTo 4 = {2, 3} := by decide +kernel
  refine ⟨hb, by decide +kernel, ?_⟩
  ext r
  simp only [mem_escapingSquareOffsets, SquareOffsetCovered, hb, SquareOffsetForbiddenBy]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
  simp only [SquareOffset, Nat.dvd_iff_mod_eq_zero]
  omega

theorem four_survivor_filter :
    squareShellWheelSurvivorImage 4 = {1, 5} := by
  classical
  rw [squareShell_survivor_filter_eq_image_escaping (by decide), four_basis_and_image.2.2]
  decide +kernel

theorem four_multiplicity :
    (squareShellWheelSurvivorImage 4).card = 2 ∧
    (paritySafeUncoveredCandidates 4).card = 3 := by
  rw [four_survivor_filter, ← escapingSquareOffsets_eq_paritySafeUncovered (by decide : 2 ≤ 4),
    four_basis_and_image.2.2]
  decide

theorem four_one_residue_and_survivor :
    ¬SquareOffsetCovered 4 1 ∧
    IsPrimeBasisWheelSurvivor (primeScalesUpTo 4)
      (squareShellWheelProjection (primeScalesUpTo 4) 4 1) := by
  have hs := primorialWheelBridge_four_one.2.2.2
  exact ⟨(not_squareOffsetCovered_iff_projection_survivor (by decide)).mpr hs, hs⟩

/-- n=1 loses the prime 2 under parity restriction and has no projected survivor. -/
theorem one_carrier_boundary : (escapingSquareOffsets 1).card = 2 ∧
    (paritySafeUncoveredCandidates 1).card = 1 ∧
    ¬∃ x ∈ squareShellWheelImage 1, IsPrimeBasisWheelSurvivor (primeScalesUpTo 1) x := by
  constructor
  · have he : escapingSquareOffsets 1 = {1, 2} := by
      ext r
      have hb : primeScalesUpTo 1 = ∅ := by decide +kernel
      simp only [mem_escapingSquareOffsets, SquareOffsetCovered, hb, Finset.notMem_empty,
        false_and, exists_false, not_false_eq_true, and_true, SquareOffset,
        Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he]; decide
  constructor
  · simp only [paritySafeUncoveredCandidates, paritySafeCoveredCandidates, paritySafeActiveSupport]
    decide +kernel
  · rintro ⟨x, hx, hs⟩
    have hM := small_periods.1
    change 0 < x ∧ x < finitePrimeBasisProduct (primeScalesUpTo 1) ∧ _ at hs
    rw [hM] at hs
    omega

/-- The least repeated-case owner is not necessarily the repeated prime. -/
theorem repeated_eight_owner : squareResidueCoverOwner 8 11 = 3 ∧
    paritySafeActiveSupport 8 11 = {3, 5} ∧
    25 ∈ sqrtRoughRoutedFiber 8 3 ∧ 15 ∈ sqrtRoughRoutedFiber 8 5 := by
  have ho := sqrt_repeated_residue_owner repeated_eight_key
  have hs := (sqrt_repeated_offset_packet repeated_eight_key).2
  exact ⟨ho, hs, repeated_eight_quotients⟩

theorem repeated_prime_twentyNine_owner : squareResidueCoverOwner 29 6 = 7 ∧
    squareResidueCoverOwner 29 6 ≠ 11 := by
  have h := sqrt_repeated_residue_owner repeated_upper_key
  norm_num [sqrtRepeatedProduct] at h
  exact ⟨h, by omega⟩

theorem repeated_thirteen_owner : squareResidueCoverOwner 13 6 = 5 ∧
    35 ∈ sqrtRoughRoutedFiber 13 5 ∧ 25 ∈ sqrtRoughRoutedFiber 13 7 :=
  ⟨sqrt_repeated_residue_owner repeated_lower_key, repeated_thirteen_quotients⟩

theorem triple_nineteen_owner : squareResidueCoverOwner 19 24 = 5 ∧
    77 ∈ sqrtRoughRoutedFiber 19 5 ∧ 55 ∈ sqrtRoughRoutedFiber 19 7 ∧
    35 ∈ sqrtRoughRoutedFiber 19 11 :=
  ⟨sqrt_triple_residue_owner triple_key_nineteen, triple_nineteen_quotients⟩

theorem cube_cross_owner : squareResidueCoverOwner 5 2 = 3 ∧
    squareResidueCoverOwner 7 2 = 3 :=
  ⟨sqrt_cube_residue_owner cube_key_five, sqrt_cross_residue_owner cross_key_seven⟩

theorem rejected_eleven_two_levels : SquareOffsetCovered 11 14 ∧
    ReservedByPrimeBasis (primeScalesUpTo (Nat.sqrt 11))
      (primeBasisWheelProjection (primeScalesUpTo (Nat.sqrt 11)) 27) ∧
    14 ∈ squareResidueCoverFiber 11 5 := by
  have h := sqrt_two_level_reservation_packet rejected_eleven_packet.1 rejected_eleven_packet.2.1
  refine ⟨h.1, (sqrt_rejected_iff_quotient_wheel_reserved rejected_eleven_packet.1
    rejected_eleven_packet.2.1).mp rejected_eleven, ?_⟩
  exact (mem_squareResidueCoverFiber (by decide)).mpr ⟨by norm_num [SquareOffset], by decide⟩

/-- An actual covered lower channel changes least owners 5→2→3; all three seats are covered. -/
theorem three_lower_owners : squareResidueCoverOwner 13 6 = 5 ∧
    squareResidueCoverOwner 14 6 = 2 ∧ squareResidueCoverOwner 15 6 = 3 ∧
    SquareOffsetCovered 13 6 ∧ SquareOffsetCovered 14 6 ∧ SquareOffsetCovered 15 6 := by
  refine ⟨repeated_thirteen_owner.1, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [squareResidueCoverOwner]
  · norm_num [squareResidueCoverOwner]
  · exact ⟨5, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩, by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨2, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩, by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨3, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩, by norm_num [SquareOffsetForbiddenBy]⟩

/-- Common support can persist when the least owner changes (5 survives, 2 takes ownership). -/
theorem lower_support_persists_without_owner :
    5 ∈ squareOffsetPrimeSupport 7 6 ∩ squareOffsetPrimeSupport 8 6 ∧
    squareResidueCoverOwner 7 6 = 5 ∧ squareResidueCoverOwner 8 6 = 2 := by
  constructor
  · rw [Finset.mem_inter, mem_squareOffsetPrimeSupport, mem_squareOffsetPrimeSupport]
    norm_num
  · norm_num [squareResidueCoverOwner]

theorem sqrt_primorial_address_not_above_anchor :
    Nat.sqrt (finitePrimeBasisProduct (primeScalesUpTo 6)) = 5 ∧
    Nat.sqrt (finitePrimeBasisProduct (primeScalesUpTo 6)) < 6 := by
  rw [small_periods.2.2.2.2.2.1]
  decide +kernel

end DkMathTest.LegendreResidueCoverRegression
