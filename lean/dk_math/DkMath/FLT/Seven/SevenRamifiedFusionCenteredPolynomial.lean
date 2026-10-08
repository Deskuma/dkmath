/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

/-- The common natural sextic in the center coordinate. -/
def centeredSevenSextic (D q : ℕ) : ℕ :=
  7 * q ^ 6 + 35 * D ^ 2 * q ^ 4 + 21 * D ^ 4 * q ^ 2 + D ^ 6

theorem centeredSevenSextic_intCast (D q : ℕ) :
    (centeredSevenSextic D q : ℤ) =
      7 * (q : ℤ) ^ 6 + 35 * (D : ℤ) ^ 2 * (q : ℤ) ^ 4 +
        21 * (D : ℤ) ^ 4 * (q : ℤ) ^ 2 + (D : ℤ) ^ 6 := by
  simp only [centeredSevenSextic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Signed subtraction stays in integers. No division by the gap is used. -/
theorem centered_seventh_power_difference (x D : ℤ) :
    64 * ((x + D) ^ 7 - x ^ 7) =
      D * (7 * (2 * x + D) ^ 6 + 35 * D ^ 2 * (2 * x + D) ^ 4 +
        21 * D ^ 4 * (2 * x + D) ^ 2 + D ^ 6) := by
  ring

theorem GN_seven_centered_identity (D u : ℕ) :
    64 * GN 7 D u = centeredSevenSextic D (D + 2 * u) := by
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  unfold centeredSevenSextic
  ring

theorem alternatingCyclotomicSeven_centered_identity {u v : ℕ} (horder : u ≤ v) :
    64 * alternatingCyclotomicSeven u v = centeredSevenSextic (u + v) (v - u) := by
  apply Int.ofNat_injective
  change ((64 * alternatingCyclotomicSeven u v : ℕ) : ℤ) =
    (centeredSevenSextic (u + v) (v - u) : ℤ)
  push_cast
  rw [alternatingCyclotomicSeven_intCast, centeredSevenSextic_intCast]
  rw [Int.natCast_sub horder]
  simp only [cyclotomicSeven, Nat.cast_add]
  ring

theorem centeredSevenSextic_strictMono (D : ℕ) : StrictMono (centeredSevenSextic D) := by
  intro a b hab
  have h6 := Nat.mul_lt_mul_of_pos_left
    ((Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mpr hab) (by decide : 0 < 7)
  have h4 := Nat.mul_le_mul_left (35 * D ^ 2) (Nat.pow_le_pow_left hab.le 4)
  have h2 := Nat.mul_le_mul_left (21 * D ^ 4) (Nat.pow_le_pow_left hab.le 2)
  unfold centeredSevenSextic
  omega

theorem centeredSevenSextic_at_gap (D : ℕ) : centeredSevenSextic D D = 64 * D ^ 6 := by
  unfold centeredSevenSextic
  ring

theorem centeredSevenSextic_target_unique {D q₁ q₂ target : ℕ}
    (h₁ : centeredSevenSextic D q₁ = target) (h₂ : centeredSevenSextic D q₂ = target) :
    q₁ = q₂ := (centeredSevenSextic_strictMono D).injective (h₁.trans h₂.symm)

/-- Exact scalar equivalence, including the zero-endpoint boundary. -/
theorem GN_seven_eq_iff_centered {D u target : ℕ} :
    GN 7 D u = target ↔ centeredSevenSextic D (D + 2 * u) = 64 * target := by
  rw [← GN_seven_centered_identity]
  exact (Nat.mul_left_cancel_iff (by decide : 0 < 64)).symm

theorem alternatingCyclotomicSeven_eq_iff_centered {u v target : ℕ} (horder : u ≤ v) :
    alternatingCyclotomicSeven u v = target ↔
      centeredSevenSextic (u + v) (v - u) = 64 * target := by
  rw [← alternatingCyclotomicSeven_centered_identity horder]
  exact (Nat.mul_left_cancel_iff (by decide : 0 < 64)).symm

theorem nestedGNResidual_centered {r s u : ℕ} (hu : 0 < u)
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    centeredSevenSextic (7 ^ 27 * r ^ 49) (7 ^ 27 * r ^ 49 + 2 * u) =
      64 * (7 * s ^ 49) ∧ 7 ^ 27 * r ^ 49 < 7 ^ 27 * r ^ 49 + 2 * u := by
  exact ⟨GN_seven_eq_iff_centered.mp hGN, by omega⟩

theorem nestedAlternatingResidual_centered {r s u v : ℕ} (hu : 0 < u)
    (horder : u ≤ v) (hsum : u + v = 7 ^ 27 * r ^ 49)
    (hAlt : alternatingCyclotomicSeven u v = 7 * s ^ 49) :
    centeredSevenSextic (7 ^ 27 * r ^ 49) (v - u) = 64 * (7 * s ^ 49) ∧
      v - u < 7 ^ 27 * r ^ 49 := by
  exact ⟨by simpa only [hsum] using (alternatingCyclotomicSeven_eq_iff_centered horder).mp hAlt,
    by omega⟩

/-- The old threshold is exactly the position of a solution center relative
to the gap. This does not provide a solution center. -/
theorem nestedCentered_allocation_threshold {M r s q : ℕ} (hr : 0 < r)
    (hM : M = r * s)
    (hP : centeredSevenSextic (7 ^ 27 * r ^ 49) q = 64 * (7 * s ^ 49)) :
    (7 ^ 27 * r ^ 49 < q ↔ 7 ^ 161 * r ^ 343 < M ^ 49) ∧
      (q < 7 ^ 27 * r ^ 49 ↔ M ^ 49 < 7 ^ 161 * r ^ 343) := by
  have hcomp := nestedAllocation_threshold_comparisons hr hM
  have hgt : 7 ^ 27 * r ^ 49 < q ↔ (7 ^ 27 * r ^ 49) ^ 6 < 7 * s ^ 49 := by
    rw [← (centeredSevenSextic_strictMono (7 ^ 27 * r ^ 49)).lt_iff_lt,
      hP, centeredSevenSextic_at_gap, Nat.mul_lt_mul_left (by decide : 0 < 64)]
  have hlt : q < 7 ^ 27 * r ^ 49 ↔ 7 * s ^ 49 < (7 ^ 27 * r ^ 49) ^ 6 := by
    rw [← (centeredSevenSextic_strictMono (7 ^ 27 * r ^ 49)).lt_iff_lt,
      hP, centeredSevenSextic_at_gap, Nat.mul_lt_mul_left (by decide : 0 < 64)]
  exact ⟨hgt.trans hcomp.1, hlt.trans hcomp.2⟩

theorem GN_seven_endpoint_unique_via_center {D u v target : ℕ}
    (hu : GN 7 D u = target) (hv : GN 7 D v = target) : u = v := by
  have hq := centeredSevenSextic_target_unique (GN_seven_eq_iff_centered.mp hu)
    (GN_seven_eq_iff_centered.mp hv)
  omega

/-- Equal alternating residuals at a fixed sum have a unique ordered pair.
The orientation premises are essential. -/
theorem alternatingCyclotomicSeven_ordered_endpoint_unique {D u v u' v' target : ℕ}
    (hsum : u + v = D) (hsum' : u' + v' = D) (horder : u ≤ v) (horder' : u' ≤ v')
    (hAlt : alternatingCyclotomicSeven u v = target)
    (hAlt' : alternatingCyclotomicSeven u' v' = target) : u = u' ∧ v = v' := by
  have h₁ : centeredSevenSextic D (v - u) = 64 * target := by
    simpa only [hsum] using (alternatingCyclotomicSeven_eq_iff_centered horder).mp hAlt
  have h₂ : centeredSevenSextic D (v' - u') = 64 * target := by
    simpa only [hsum'] using (alternatingCyclotomicSeven_eq_iff_centered horder').mp hAlt'
  have hq := centeredSevenSextic_target_unique h₁ h₂
  omega

/-- Explicit provenance distinguishes the two charts, retains parity,
positive primitive endpoints and canonical alternating orientation, and
excludes the degenerate center q = D. -/
def CenteredNestedAllocationCandidate (M r q : ℕ) : Prop :=
  let D := 7 ^ 27 * r ^ 49
  Nat.ModEq 2 q D ∧ centeredSevenSextic D q = 64 * (7 * (M / r) ^ 49) ∧
    ((D < q ∧ ∃ u : ℕ, 0 < u ∧ Nat.Coprime u (7 * M) ∧ q = D + 2 * u) ∨
      (q < D ∧ ∃ u : ℕ, 0 < u ∧ u < D ∧ u ≤ D - u ∧
        Nat.Coprime u D ∧ D - q = 2 * u))

theorem centeredNestedAllocationCandidate_unique {M r q₁ q₂ : ℕ}
    (h₁ : CenteredNestedAllocationCandidate M r q₁)
    (h₂ : CenteredNestedAllocationCandidate M r q₂) : q₁ = q₂ :=
  centeredSevenSextic_target_unique h₁.2.1 h₂.2.1

theorem centeredNestedAllocationCandidate_ne_gap {M r q : ℕ}
    (h : CenteredNestedAllocationCandidate M r q) : q ≠ 7 ^ 27 * r ^ 49 := by
  rcases h.2.2 with h | h <;> omega

theorem nestedRHSAllocation_iff_ordered (M r : ℕ) :
    NestedRHSAllocationCondition M r ↔
      ∃ u : ℕ, 0 < u ∧ u < 7 ^ 27 * r ^ 49 ∧ u ≤ 7 ^ 27 * r ^ 49 - u ∧
        Nat.Coprime u (7 ^ 27 * r ^ 49) ∧
        alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * (M / r) ^ 49 := by
  constructor
  · rintro ⟨u, hu, huD, hcop, hAlt⟩
    by_cases horder : u ≤ 7 ^ 27 * r ^ 49 - u
    · exact ⟨u, hu, huD, horder, hcop, hAlt⟩
    · have hv : 0 < 7 ^ 27 * r ^ 49 - u := by omega
      have hvD : 7 ^ 27 * r ^ 49 - u < 7 ^ 27 * r ^ 49 := by omega
      have hswap : 7 ^ 27 * r ^ 49 - (7 ^ 27 * r ^ 49 - u) = u := by omega
      refine ⟨7 ^ 27 * r ^ 49 - u, hv, hvD, by omega,
        (Nat.coprime_self_sub_left huD.le).mpr hcop, ?_⟩
      rw [hswap, alternatingCyclotomicSeven_comm]
      exact hAlt
  · rintro ⟨u, hu, huD, _, hcop, hAlt⟩
    exact ⟨u, hu, huD, hcop, hAlt⟩

/-- The center and gap have equal parity in the GN chart. -/
theorem centeredGNCoordinate_parity (D u : ℕ) : Nat.ModEq 2 (D + 2 * u) D := by
  unfold Nat.ModEq
  omega

/-- The ordered alternating difference has the sum's parity. -/
theorem centeredAlternatingCoordinate_parity {D u : ℕ} (horder : u ≤ D - u) :
    Nat.ModEq 2 (D - u - u) D := by
  unfold Nat.ModEq
  omega

/-- Exact natural reconstruction of the ordered difference from the sum. -/
theorem centeredAlternatingCoordinate_eq {D u q : ℕ} (hqD : q < D)
    (hqu : D - q = 2 * u) : D - u - u = q := by
  omega

theorem centeredAlternatingCoordinate_sum {D u : ℕ} (horder : u ≤ D - u) :
    D - (D - u - u) = 2 * u := by
  omega

theorem nestedGNAllocation_iff_centered (M r : ℕ) :
    NestedGNAllocationCondition M r ↔
      ∃ q : ℕ, CenteredNestedAllocationCandidate M r q ∧ 7 ^ 27 * r ^ 49 < q := by
  constructor
  · rintro ⟨u, hu, hcop, hGN⟩
    have hcenter := nestedGNResidual_centered hu hGN
    refine ⟨7 ^ 27 * r ^ 49 + 2 * u, ⟨?_, hcenter.1,
      .inl ⟨hcenter.2, u, hu, hcop, rfl⟩⟩, hcenter.2⟩
    exact centeredGNCoordinate_parity _ _
  · rintro ⟨q, hcenter, hgt⟩
    rcases hcenter.2.2 with ⟨_, u, hu, hcop, hq⟩ | h
    · refine ⟨u, hu, hcop, GN_seven_eq_iff_centered.mpr ?_⟩
      simpa only [hq] using hcenter.2.1
    · exact False.elim (not_lt_of_gt hgt h.1)

theorem nestedRHSAllocation_iff_centered (M r : ℕ) :
    NestedRHSAllocationCondition M r ↔
      ∃ q : ℕ, CenteredNestedAllocationCandidate M r q ∧ q < 7 ^ 27 * r ^ 49 := by
  rw [nestedRHSAllocation_iff_ordered]
  constructor
  · rintro ⟨u, hu, huD, horder, hcop, hAlt⟩
    have hsum : u + (7 ^ 27 * r ^ 49 - u) = 7 ^ 27 * r ^ 49 := Nat.add_sub_of_le huD.le
    have hcenter := nestedAlternatingResidual_centered hu horder hsum hAlt
    refine ⟨7 ^ 27 * r ^ 49 - u - u, ⟨?_, hcenter.1,
      .inr ⟨hcenter.2, u, hu, huD, horder, hcop, centeredAlternatingCoordinate_sum horder⟩⟩, hcenter.2⟩
    exact centeredAlternatingCoordinate_parity horder
  · rintro ⟨q, hcenter, hlt⟩
    rcases hcenter.2.2 with h | ⟨_, u, hu, huD, horder, hcop, hq⟩
    · exact False.elim (not_lt_of_gt hlt h.1)
    · refine ⟨u, hu, huD, horder, hcop,
        (alternatingCyclotomicSeven_eq_iff_centered horder).mpr ?_⟩
      have hsum : u + (7 ^ 27 * r ^ 49 - u) = 7 ^ 27 * r ^ 49 := Nat.add_sub_of_le huD.le
      have hdiff : 7 ^ 27 * r ^ 49 - u - u = q := centeredAlternatingCoordinate_eq hlt hq
      simpa only [hsum, hdiff] using hcenter.2.1

theorem nestedAllocation_iff_centered (M r : ℕ) :
    (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) ↔
      ∃ q : ℕ, CenteredNestedAllocationCandidate M r q := by
  rw [nestedGNAllocation_iff_centered, nestedRHSAllocation_iff_centered]
  constructor
  · rintro (⟨q, h, _⟩ | ⟨q, h, _⟩) <;> exact ⟨q, h⟩
  · rintro ⟨q, h⟩
    rcases h.2.2 with hchart | hchart
    · exact .inl ⟨q, h, hchart.1⟩
    · exact .inr ⟨q, h, hchart.1⟩

/-- The 048 allocation filters and selected-branch guards are retained.
The exact scalar equation is searched in one canonical center coordinate. -/
def SixthPowerSievedCenteredCondition (M : ℕ) : Prop :=
  ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 7 (M / r) 1 ∧ SixthPowerAllocationSieve r (M / r) ∧
    ∃ q : ℕ, CenteredNestedAllocationCandidate M r q ∧
      ((7 ^ 161 * r ^ 343 < M ^ 49 ∧ 7 ^ 27 * r ^ 49 < q) ∨
        (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49 ∧
          q < 7 ^ 27 * r ^ 49))

theorem sixthPowerSievedNestedCondition_iff_centered (M : ℕ) :
    SixthPowerSievedNestedCondition M ↔ SixthPowerSievedCenteredCondition M := by
  constructor
  · rintro ⟨r, hmem, hcop, hsize, h7, hsixth, hbranch⟩
    refine ⟨r, hmem, hcop, hsize, h7, hsixth, ?_⟩
    rcases hbranch with ⟨hgt, hGN⟩ | ⟨hlt, hband, hRHS⟩
    · rcases (nestedGNAllocation_iff_centered M r).mp hGN with ⟨q, h, hq⟩
      exact ⟨q, h, .inl ⟨hgt, hq⟩⟩
    · rcases (nestedRHSAllocation_iff_centered M r).mp hRHS with ⟨q, h, hq⟩
      exact ⟨q, h, .inr ⟨hlt, hband, hq⟩⟩
  · rintro ⟨r, hmem, hcop, hsize, h7, hsixth, q, h, hbranch⟩
    refine ⟨r, hmem, hcop, hsize, h7, hsixth, ?_⟩
    rcases hbranch with ⟨hgt, hq⟩ | ⟨hlt, hband, hq⟩
    · exact .inl ⟨hgt, (nestedGNAllocation_iff_centered M r).mpr ⟨q, h, hq⟩⟩
    · exact .inr ⟨hlt, hband, (nestedRHSAllocation_iff_centered M r).mpr ⟨q, h, hq⟩⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourReconstruction_iff_centered (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      SixthPowerSievedCenteredCondition (internalDepthFourSeventhCore p) := by
  rw [internalDepthFourReconstruction_iff_sixth_power_sieved,
    sixthPowerSievedNestedCondition_iff_centered]

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
