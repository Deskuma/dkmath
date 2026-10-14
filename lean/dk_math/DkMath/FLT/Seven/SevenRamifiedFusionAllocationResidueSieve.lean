/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The finite-field unit calculation, without any lifting assumption. -/
theorem sixth_power_mod_seven_of_unit {w : ℕ} (hw : ¬ 7 ∣ w) :
    Nat.ModEq 7 (w ^ 6) 1 := by
  have hcop := (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr hw
  simpa using Nat.ModEq.pow_card_sub_one_eq_one (by norm_num : Nat.Prime 7) hcop.symm

/-- Twice applying Frobenius leaves a natural forty-ninth power unchanged
modulo seven, including the zero residue. -/
theorem fortyNinth_power_mod_seven (s : ℕ) : Nat.ModEq 7 (s ^ 49) s := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  exact ZMod.pow_card_pow (n := 2) (s : ZMod 7)

/-- Two finite binomial carries lift the residue one from modulus seven
to modulus 343 after taking a forty-ninth power. -/
theorem fortyNinth_power_mod_seven_cube_of_one {s : ℕ} (hs : Nat.ModEq 7 s 1) :
    Nat.ModEq (7 ^ 3) (s ^ 49) 1 := by
  rcases hs.symm.dvd with ⟨k, hk⟩
  have hsInt : (s : ℤ) = 1 + 7 * k := by norm_num at hk; linarith
  let Q : ℤ := k + 3 * 7 * k ^ 2 + 5 * 7 ^ 2 * k ^ 3 +
    5 * 7 ^ 3 * k ^ 4 + 3 * 7 ^ 4 * k ^ 5 + 7 ^ 5 * k ^ 6 + 7 ^ 5 * k ^ 7
  have hseven : (s : ℤ) ^ 7 = 1 + 49 * Q := by
    rw [hsInt]
    dsimp [Q]
    ring
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨-(Q + 3 * 7 ^ 2 * Q ^ 2 + 5 * 7 ^ 4 * Q ^ 3 +
    5 * 7 ^ 6 * Q ^ 4 + 3 * 7 ^ 8 * Q ^ 5 + 7 ^ 10 * Q ^ 6 + 7 ^ 11 * Q ^ 7), ?_⟩
  push_cast
  rw [show (s : ℤ) ^ 49 = ((s : ℤ) ^ 7) ^ 7 by rw [← pow_mul], hseven]
  ring

/-- Independent common consequences of the full-gap congruence: the
complementary allocation is one mod seven and the endpoint's sixth power
is one mod 343. These are necessary conditions, not exact receivers. -/
theorem nested_full_gap_residue_sieve {r s w : ℕ} (hw : ¬ 7 ∣ w)
    (h : Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (w ^ 6)) :
    Nat.ModEq 7 s 1 ∧ Nat.ModEq (7 ^ 3) (w ^ 6) 1 := by
  have h7 : 7 ∣ 7 ^ 27 * r ^ 49 := dvd_mul_of_dvd_left (by norm_num) _
  have h343 : 7 ^ 3 ∣ 7 ^ 27 * r ^ 49 := by use 7 ^ 24 * r ^ 49; ring
  have hs := (fortyNinth_power_mod_seven s).symm.trans
    ((h.of_dvd h7).trans (sixth_power_mod_seven_of_unit hw))
  exact ⟨hs, (h.of_dvd h343).symm.trans (fortyNinth_power_mod_seven_cube_of_one hs)⟩

theorem nestedGNResidual_residue_sieve {M r s u : ℕ}
    (hcop : Nat.Coprime u (7 * M))
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    Nat.ModEq 7 s 1 ∧ Nat.ModEq (7 ^ 3) (u ^ 6) 1 := by
  have hu7 : ¬ 7 ∣ u := (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mp
    (hcop.of_dvd_right (dvd_mul_right 7 M)).symm
  exact nested_full_gap_residue_sieve hu7 (nestedResidual_full_gap_congruence hGN)

theorem nestedAlternatingResidual_residue_sieve {r s u : ℕ}
    (huD : u < 7 ^ 27 * r ^ 49) (hcop : Nat.Coprime u (7 ^ 27 * r ^ 49))
    (hAlt : alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49) :
    Nat.ModEq 7 s 1 ∧ Nat.ModEq (7 ^ 3) (u ^ 6) 1 := by
  have h7 : 7 ∣ 7 ^ 27 * r ^ 49 := dvd_mul_of_dvd_left (by norm_num) _
  have hu7 : ¬ 7 ∣ u := (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mp
    (hcop.of_dvd_right h7).symm
  have hsum : (7 ^ 27 * r ^ 49 - u) + u = 7 ^ 27 * r ^ 49 := by omega
  have hAlt' : alternatingCyclotomicSeven (7 ^ 27 * r ^ 49 - u) u = 7 * s ^ 49 := by
    rw [alternatingCyclotomicSeven_comm]; exact hAlt
  exact nested_full_gap_residue_sieve hu7
    (nestedAlternatingResidual_full_sum_congruence hsum hAlt').2

theorem nestedAllocation_residue_sieve {M r : ℕ}
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 7 (M / r) 1 := by
  rcases h with ⟨u, _, hcop, hGN⟩ | ⟨u, _, huD, hcop, hAlt⟩
  · exact (nestedGNResidual_residue_sieve hcop hGN).1
  · exact (nestedAlternatingResidual_residue_sieve huD hcop hAlt).1

/-- A failed endpoint-independent residue test excludes both exact branches
at this allocation, even without source positivity or seven-unit premises. -/
theorem nestedAllocation_excluded_of_residue {M r : ℕ}
    (hbad : ¬ Nat.ModEq 7 (M / r) 1) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  fun h => hbad (nestedAllocation_residue_sieve h)

/-- Unit cancellation transports the complementary residue filter into
the equivalent congruence of the divisor and source core. -/
theorem nestedAllocation_residue_iff {M r s : ℕ} (hM : M = r * s) (hr : ¬ 7 ∣ r) :
    Nat.ModEq 7 s 1 ↔ Nat.ModEq 7 r M := by
  constructor
  · intro h
    simpa only [mul_one, ← hM] using (h.mul_left r).symm
  · intro h
    have hcop := (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr hr
    apply Nat.ModEq.cancel_left_of_coprime hcop
    simpa only [mul_one, hM] using h.symm

/-- The alternating finite-power estimate yields an integral band around
the strict threshold, with the upper end inclusive. -/
theorem nestedAlternatingResidual_allocation_band {M r s u : ℕ}
    (hr : 0 < r) (hu : 0 < u) (huD : u < 7 ^ 27 * r ^ 49) (hM : M = r * s)
    (hAlt : alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49) :
    M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49 := by
  refine ⟨nestedAlternatingResidual_allocation_threshold hr hu huD hM hAlt, ?_⟩
  have hsum : u + (7 ^ 27 * r ^ 49 - u) = 7 ^ 27 * r ^ 49 := Nat.add_sub_of_le huD.le
  have hle := sum_pow_six_le_sixtyFour_mul_alternatingCyclotomicSeven
    (by omega : 0 < u + (7 ^ 27 * r ^ 49 - u))
  rw [hsum, hAlt] at hle
  have hD : (7 ^ 27 * r ^ 49) ^ 6 = 7 * (7 ^ 161 * r ^ 294) := by
    simp only [mul_pow, ← pow_mul]
    ring
  have hsub : 7 ^ 161 * r ^ 294 ≤ 64 * s ^ 49 := by
    apply le_of_mul_le_mul_left (a := 7) _ (by decide : 0 < 7)
    simpa only [hD, mul_assoc, mul_left_comm 64 7] using hle
  calc
    _ = r ^ 49 * (7 ^ 161 * r ^ 294) := by ring
    _ ≤ r ^ 49 * (64 * s ^ 49) := Nat.mul_le_mul_left _ hsub
    _ = _ := by rw [hM, mul_pow]; ring

theorem nestedRHSAllocation_band {M r : ℕ} (hM : 0 < M) (hdiv : r ∣ M)
    (h : NestedRHSAllocationCondition M r) :
    M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49 := by
  rcases h with ⟨u, hu, huD, _, hAlt⟩
  exact nestedAlternatingResidual_allocation_band (Nat.pos_of_dvd_of_pos hdiv hM)
    hu huD (Nat.mul_div_cancel' hdiv).symm hAlt

/-- Endpoint-independent residue, size and threshold tests precede the
existing exact scalar equations. No endpoint equation defines this sieve. -/
def ResidueSievedNestedCondition (M : ℕ) : Prop :=
  ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 7 (M / r) 1 ∧
    ((7 ^ 161 * r ^ 343 < M ^ 49 ∧ NestedGNAllocationCondition M r) ∨
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49 ∧
        NestedRHSAllocationCondition M r))

theorem thresholdRoutedNestedCondition_iff_residue_sieved (M : ℕ) (hM : 0 < M) :
    ThresholdRoutedNestedCondition M ↔ ResidueSievedNestedCondition M := by
  constructor
  · rintro ⟨r, hmem, hcop, hsize, h⟩
    have hbranch : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r :=
      h.elim (fun h => .inl h.2) (fun h => .inr h.2)
    refine ⟨r, hmem, hcop, hsize, nestedAllocation_residue_sieve hbranch, ?_⟩
    rcases h with ⟨hlt, hGN⟩ | ⟨hlt, hRHS⟩
    · exact .inl ⟨hlt, hGN⟩
    · exact .inr ⟨hlt, (nestedRHSAllocation_band hM (Nat.dvd_of_mem_divisors hmem) hRHS).2, hRHS⟩
  · rintro ⟨r, hmem, hcop, hsize, _, h⟩
    refine ⟨r, hmem, hcop, hsize, ?_⟩
    rcases h with ⟨hlt, hGN⟩ | ⟨hlt, _, hRHS⟩
    · exact .inl ⟨hlt, hGN⟩
    · exact .inr ⟨hlt, hRHS⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourReconstruction_iff_residue_sieved
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      ResidueSievedNestedCondition (internalDepthFourSeventhCore p) := by
  rw [internalDepthFourReconstruction_iff_threshold_routed,
    thresholdRoutedNestedCondition_iff_residue_sieved _ (internalDepthFourSeventhCore_pos p)]

theorem internalDepthFourAllocation_residue_iff (p : RamifiedSignedRootRoutingPacket)
    {r : ℕ} (hmem : r ∈ (internalDepthFourSeventhCore p).divisors) :
    Nat.ModEq 7 (internalDepthFourSeventhCore p / r) 1 ↔
      Nat.ModEq 7 r (internalDepthFourSeventhCore p) :=
  nestedAllocation_residue_iff (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hmem)).symm
    (internalDepthFourAllocation_seven_units p hmem).1

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
