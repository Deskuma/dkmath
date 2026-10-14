/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSymmetricReconstruction
import Mathlib.Algebra.Order.Ring.Basic

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

/-- Positive GN endpoints lie strictly above the zero-endpoint residual. -/
theorem GN_seven_gap_pow_six_lt {D u : ℕ} (hu : 0 < u) :
    D ^ 6 < GN 7 D u := by
  have hzero : GN 7 D 0 = D ^ 6 := by
    rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
    simp
    ring
  rw [← hzero]
  exact GN_seven_unit_strictMono D hu

/-- For positive endpoints the alternating residual is strictly below
the sixth power of their sum. This uses natural inequalities only. -/
theorem alternatingCyclotomicSeven_lt_sum_pow_six {x y : ℕ}
    (hx : 0 < x) (hy : 0 < y) :
    alternatingCyclotomicSeven x y < (x + y) ^ 6 := by
  have hxlt : x < x + y := Nat.lt_add_of_pos_right hy
  have hylt : y < x + y := by omega
  have hxpow : x ^ 6 < (x + y) ^ 6 :=
    (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mpr hxlt
  have hypow : y ^ 6 < (x + y) ^ 6 :=
    (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mpr hylt
  have hsum : x ^ 7 + y ^ 7 < (x + y) * (x + y) ^ 6 := by
    calc
      _ = x * x ^ 6 + y * y ^ 6 := by ring
      _ < x * (x + y) ^ 6 + y * (x + y) ^ 6 :=
        Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left hxpow hx)
          (Nat.mul_lt_mul_of_pos_left hypow hy)
      _ = _ := by ring
  apply (Nat.mul_lt_mul_left (by omega : 0 < x + y)).mp
  rw [add_mul_alternatingCyclotomicSeven]
  exact hsum

/-- The finite exponent-seven power inequality supplies the common coarse
lower estimate for the alternating residual. -/
theorem sum_pow_six_le_sixtyFour_mul_alternatingCyclotomicSeven {x y : ℕ}
    (hpos : 0 < x + y) :
    (x + y) ^ 6 ≤ 64 * alternatingCyclotomicSeven x y := by
  have hpower : (x + y) ^ 7 ≤ 64 * (x ^ 7 + y ^ 7) := by
    simpa using add_pow_le (Nat.zero_le x) (Nat.zero_le y) 7
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (x + y) * (x + y) ^ 6 = (x + y) ^ 7 := by ring
    _ ≤ 64 * (x ^ 7 + y ^ 7) := hpower
    _ = (x + y) * (64 * alternatingCyclotomicSeven x y) := by
      rw [← add_mul_alternatingCyclotomicSeven]
      ring

/-- Exact exponent arithmetic transports the residual threshold into the
source allocation currency, in either strict direction. -/
theorem nestedAllocation_threshold_comparisons {M r s : ℕ}
    (hr : 0 < r) (hM : M = r * s) :
    ((7 ^ 27 * r ^ 49) ^ 6 < 7 * s ^ 49 ↔ 7 ^ 161 * r ^ 343 < M ^ 49) ∧
      (7 * s ^ 49 < (7 ^ 27 * r ^ 49) ^ 6 ↔ M ^ 49 < 7 ^ 161 * r ^ 343) := by
  have hD : (7 ^ 27 * r ^ 49) ^ 6 = 7 * (7 ^ 161 * r ^ 294) := by
    simp only [mul_pow, ← pow_mul]
    ring
  have hleft : r ^ 49 * (7 ^ 161 * r ^ 294) = 7 ^ 161 * r ^ 343 := by ring
  have hright : r ^ 49 * s ^ 49 = M ^ 49 := by rw [hM, mul_pow]
  have hr49 : 0 < r ^ 49 := pow_pos hr 49
  rw [hD]
  constructor
  · rw [Nat.mul_lt_mul_left (by decide : 0 < 7)]
    rw [← hleft, ← hright]
    exact (Nat.mul_lt_mul_left hr49).symm
  · rw [Nat.mul_lt_mul_left (by decide : 0 < 7)]
    rw [← hleft, ← hright]
    exact (Nat.mul_lt_mul_left hr49).symm

theorem nestedGNResidual_allocation_threshold {M r s u : ℕ}
    (hr : 0 < r) (hu : 0 < u) (hM : M = r * s)
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    7 ^ 161 * r ^ 343 < M ^ 49 :=
  (nestedAllocation_threshold_comparisons hr hM).1.mp
    (by rw [← hGN]; exact GN_seven_gap_pow_six_lt hu)

theorem nestedAlternatingResidual_allocation_threshold {M r s u : ℕ}
    (hr : 0 < r) (hu : 0 < u) (huD : u < 7 ^ 27 * r ^ 49)
    (hM : M = r * s)
    (hAlt : alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49) :
    M ^ 49 < 7 ^ 161 * r ^ 343 := by
  apply (nestedAllocation_threshold_comparisons hr hM).2.mp
  simpa only [Nat.add_sub_of_le huD.le, hAlt] using
    alternatingCyclotomicSeven_lt_sum_pow_six hu (Nat.sub_pos_of_lt huD)

/-- The equality boundary is excluded by the source's seven-unit condition,
independently of any residual equation or endpoint. -/
theorem nestedAllocation_threshold_ne {M r : ℕ} (hM : ¬ 7 ∣ M) :
    M ^ 49 ≠ 7 ^ 161 * r ^ 343 := by
  intro heq
  apply hM
  apply (by norm_num : Nat.Prime 7).dvd_of_dvd_pow
  rw [heq]
  exact dvd_mul_of_dvd_left (by norm_num) _

theorem nestedAllocation_threshold_dichotomy {M r : ℕ} (hM : ¬ 7 ∣ M) :
    7 ^ 161 * r ^ 343 < M ^ 49 ∨ M ^ 49 < 7 ^ 161 * r ^ 343 := by
  have hne := nestedAllocation_threshold_ne (r := r) hM
  omega

/-- The coarse estimate excludes small complementary allocations without
taking approximate real roots. -/
theorem nestedResidual_coarse_allocation_bound {r s : ℕ} (hr : 0 < r)
    (hle : (7 ^ 27 * r ^ 49) ^ 6 ≤ 64 * 7 * s ^ 49) :
    7 ^ 3 * r ^ 6 < s ∧ 7 ^ 3 * r ^ 7 < r * s ∧ 343 < r * s := by
  have hs : 7 ^ 3 * r ^ 6 < s := by
    by_contra h
    have hsle : s ≤ 7 ^ 3 * r ^ 6 := by omega
    have hpow : s ^ 49 ≤ (7 ^ 3 * r ^ 6) ^ 49 := Nat.pow_le_pow_left hsle 49
    have hstrict : 64 * 7 * (7 ^ 3 * r ^ 6) ^ 49 < (7 ^ 27 * r ^ 49) ^ 6 := by
      calc
        _ = (64 * 7 ^ 148) * r ^ 294 := by
          simp only [mul_pow, ← pow_mul]
          ring
        _ < 7 ^ 162 * r ^ 294 :=
          Nat.mul_lt_mul_of_pos_right (by norm_num) (pow_pos hr 294)
        _ = _ := by simp only [mul_pow, ← pow_mul]
    have hle' := hle.trans (Nat.mul_le_mul_left (64 * 7) hpow)
    omega
  have hM : 7 ^ 3 * r ^ 7 < r * s := by
    calc
      _ = r * (7 ^ 3 * r ^ 6) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left hs hr
  have hr7 : 0 < r ^ 7 := pow_pos hr 7
  exact ⟨hs, hM, lt_of_le_of_lt (by norm_num; omega) hM⟩

theorem nestedGNResidual_coarse_allocation_bound {r s u : ℕ}
    (hr : 0 < r) (hu : 0 < u)
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    7 ^ 3 * r ^ 6 < s ∧ 7 ^ 3 * r ^ 7 < r * s ∧ 343 < r * s := by
  have hlt : (7 ^ 27 * r ^ 49) ^ 6 < 7 * s ^ 49 := by
    rw [← hGN]; exact GN_seven_gap_pow_six_lt hu
  apply nestedResidual_coarse_allocation_bound hr
  omega

theorem nestedAlternatingResidual_coarse_allocation_bound {r s u : ℕ}
    (hr : 0 < r) (hu : 0 < u) (huD : u < 7 ^ 27 * r ^ 49)
    (hAlt : alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49) :
    7 ^ 3 * r ^ 6 < s ∧ 7 ^ 3 * r ^ 7 < r * s ∧ 343 < r * s := by
  have hsum : u + (7 ^ 27 * r ^ 49 - u) = 7 ^ 27 * r ^ 49 :=
    Nat.add_sub_of_le huD.le
  have hle := sum_pow_six_le_sixtyFour_mul_alternatingCyclotomicSeven
    (by omega : 0 < u + (7 ^ 27 * r ^ 49 - u))
  rw [hsum, hAlt] at hle
  exact nestedResidual_coarse_allocation_bound hr (by simpa only [mul_assoc] using hle)

/-- Integer fixed-sum/product identity for a later half-interval order
argument. Signed subtraction is not interpreted as natural truncation. -/
theorem alternatingCyclotomicSeven_fixed_sum_product (x y : ℕ) :
    (alternatingCyclotomicSeven x y : ℤ) =
      ((x + y : ℕ) : ℤ) ^ 6 -
        7 * ((x + y : ℕ) : ℤ) ^ 4 * ((x * y : ℕ) : ℤ) +
        14 * ((x + y : ℕ) : ℤ) ^ 2 * ((x * y : ℕ) : ℤ) ^ 2 -
        7 * ((x * y : ℕ) : ℤ) ^ 3 := by
  rw [alternatingCyclotomicSeven_intCast]
  simp only [cyclotomicSeven]
  push_cast
  ring

/-- Exact GN endpoint condition for a fixed divisor allocation. -/
def NestedGNAllocationCondition (M r : ℕ) : Prop :=
  ∃ u : ℕ, 0 < u ∧ Nat.Coprime u (7 * M) ∧
    GN 7 (7 ^ 27 * r ^ 49) u = 7 * (M / r) ^ 49

/-- Exact alternating endpoint condition for the same fixed allocation. -/
def NestedRHSAllocationCondition (M r : ℕ) : Prop :=
  ∃ u : ℕ, 0 < u ∧ u < 7 ^ 27 * r ^ 49 ∧ Nat.Coprime u (7 ^ 27 * r ^ 49) ∧
    alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * (M / r) ^ 49

theorem nestedGNAllocation_threshold {M r : ℕ} (hM : 0 < M)
    (hdiv : r ∣ M) (h : NestedGNAllocationCondition M r) :
    7 ^ 161 * r ^ 343 < M ^ 49 := by
  rcases h with ⟨u, hu, _, hGN⟩
  exact nestedGNResidual_allocation_threshold (Nat.pos_of_dvd_of_pos hdiv hM)
    hu (Nat.mul_div_cancel' hdiv).symm hGN

theorem nestedRHSAllocation_threshold {M r : ℕ} (hM : 0 < M)
    (hdiv : r ∣ M) (h : NestedRHSAllocationCondition M r) :
    M ^ 49 < 7 ^ 161 * r ^ 343 := by
  rcases h with ⟨u, hu, huD, _, hAlt⟩
  exact nestedAlternatingResidual_allocation_threshold (Nat.pos_of_dvd_of_pos hdiv hM)
    hu huD (Nat.mul_div_cancel' hdiv).symm hAlt

/-- Each fixed allocation can support at most one branch, independently
of coprimality or the seven-unit boundary exclusion. -/
theorem nestedAllocation_branches_disjoint {M r : ℕ} (hM : 0 < M)
    (hdiv : r ∣ M) :
    ¬ (NestedGNAllocationCondition M r ∧ NestedRHSAllocationCondition M r) := by
  rintro ⟨hGN, hRHS⟩
  have hleft := nestedGNAllocation_threshold hM hdiv hGN
  have hright := nestedRHSAllocation_threshold hM hdiv hRHS
  omega

/-- A formula-only comparison selects the surviving branch before the
endpoint equation is considered. No receiver truth value defines this test. -/
theorem nestedAllocation_branch_selector {M r : ℕ} (hM : 0 < M)
    (hdiv : r ∣ M) :
    (7 ^ 161 * r ^ 343 < M ^ 49 → ¬ NestedRHSAllocationCondition M r) ∧
      (M ^ 49 < 7 ^ 161 * r ^ 343 → ¬ NestedGNAllocationCondition M r) := by
  constructor
  · intro hlt h
    have := nestedRHSAllocation_threshold hM hdiv h
    omega
  · intro hlt h
    have := nestedGNAllocation_threshold hM hdiv h
    omega

theorem nestedAllocation_coarse_bound {M r : ℕ} (hM : 0 < M) (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    7 ^ 3 * r ^ 6 < M / r ∧ 7 ^ 3 * r ^ 7 < M ∧ 343 < M := by
  have hr := Nat.pos_of_dvd_of_pos hdiv hM
  have hprod : M = r * (M / r) := (Nat.mul_div_cancel' hdiv).symm
  rcases h with h | h
  · rcases h with ⟨u, hu, _, hGN⟩
    simpa only [← hprod] using nestedGNResidual_coarse_allocation_bound hr hu hGN
  · rcases h with ⟨u, hu, huD, _, hAlt⟩
    simpa only [← hprod] using nestedAlternatingResidual_coarse_allocation_bound hr hu huD hAlt

theorem nestedPrescribedSummandCondition_iff_allocation (M : ℕ) (hM : 0 < M) :
    NestedPrescribedSummandCondition M ↔
      ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ NestedGNAllocationCondition M r := by
  rw [nestedPrescribedSummandCondition_iff_divisor M hM]
  constructor
  · rintro ⟨r, hmem, u, hu, hcop, huc, heq⟩
    exact ⟨r, hmem, hcop, u, hu, huc, heq⟩
  · rintro ⟨r, hmem, hcop, u, hu, huc, heq⟩
    exact ⟨r, hmem, u, hu, hcop, huc, heq⟩

/-- The right-hand-side branch now has the analogous finite divisor support. -/
theorem nestedRightHandSideCondition_iff_allocation (M : ℕ) (hM : 0 < M) :
    NestedRightHandSideCondition M ↔
      ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ NestedRHSAllocationCondition M r := by
  constructor
  · rintro ⟨r, s, u, hr, _, hu, huD, hprod, hcop, huc, heq⟩
    have hdiv : r ∣ M := ⟨s, hprod⟩
    have hsEq : M / r = s := by rw [hprod]; exact Nat.mul_div_cancel_left s hr
    refine ⟨r, Nat.mem_divisors.mpr ⟨hdiv, hM.ne'⟩, ?_, u, hu, huD, huc, ?_⟩
    · simpa only [hsEq] using hcop
    · simpa only [hsEq] using heq
  · rintro ⟨r, hmem, hcop, u, hu, huD, huc, heq⟩
    have hdiv := Nat.dvd_of_mem_divisors hmem
    have hr := Nat.pos_of_dvd_of_pos hdiv hM
    have hprod : M = r * (M / r) := (Nat.mul_div_cancel' hdiv).symm
    have hs : 0 < M / r := by
      by_contra hzero
      have hz : M / r = 0 := Nat.eq_zero_of_not_pos hzero
      rw [hz, mul_zero] at hprod
      exact hM.ne' hprod
    exact ⟨r, M / r, u, hr, hs, hu, huD, hprod, hcop, huc, heq⟩

/-- Finite factor support with a necessary coarse filter and explicit
opposite threshold tests. The residual equations remain exact obligations. -/
def ThresholdRoutedNestedCondition (M : ℕ) : Prop :=
  ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    ((7 ^ 161 * r ^ 343 < M ^ 49 ∧ NestedGNAllocationCondition M r) ∨
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ NestedRHSAllocationCondition M r))

theorem two_nested_receivers_iff_threshold_routed (M : ℕ) (hM : 0 < M) :
    (NestedPrescribedSummandCondition M ∨ NestedRightHandSideCondition M) ↔
      ThresholdRoutedNestedCondition M := by
  rw [nestedPrescribedSummandCondition_iff_allocation M hM,
    nestedRightHandSideCondition_iff_allocation M hM]
  constructor
  · intro h
    rcases h with ⟨r, hmem, hcop, hGN⟩ | ⟨r, hmem, hcop, hRHS⟩
    · have hdiv := Nat.dvd_of_mem_divisors hmem
      exact ⟨r, hmem, hcop, (nestedAllocation_coarse_bound hM hdiv (.inl hGN)).2.1,
        .inl ⟨nestedGNAllocation_threshold hM hdiv hGN, hGN⟩⟩
    · have hdiv := Nat.dvd_of_mem_divisors hmem
      exact ⟨r, hmem, hcop, (nestedAllocation_coarse_bound hM hdiv (.inr hRHS)).2.1,
        .inr ⟨nestedRHSAllocation_threshold hM hdiv hRHS, hRHS⟩⟩
  · rintro ⟨r, hmem, hcop, _, h⟩
    rcases h with ⟨_, hGN⟩ | ⟨_, hRHS⟩
    · exact .inl ⟨r, hmem, hcop, hGN⟩
    · exact .inr ⟨r, hmem, hcop, hRHS⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourAllocation_seven_units (p : RamifiedSignedRootRoutingPacket)
    {r : ℕ} (hmem : r ∈ (internalDepthFourSeventhCore p).divisors) :
    ¬ 7 ∣ r ∧ ¬ 7 ∣ internalDepthFourSeventhCore p / r := by
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hprod := Nat.mul_div_cancel' hdiv
  constructor
  · intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p (h.trans hdiv)
  · intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p
      (hprod ▸ dvd_mul_of_dvd_right h r)

/-- The actual source excludes threshold equality, so each divisor has one
strict side and the branch on the other side is impossible. This does not
assert that the remaining endpoint equation has a solution. -/
theorem internalDepthFourAllocation_strict_branch_selector
    (p : RamifiedSignedRootRoutingPacket) {r : ℕ}
    (hmem : r ∈ (internalDepthFourSeventhCore p).divisors) :
    (7 ^ 161 * r ^ 343 < internalDepthFourSeventhCore p ^ 49 ∧
      ¬ NestedRHSAllocationCondition (internalDepthFourSeventhCore p) r) ∨
    (internalDepthFourSeventhCore p ^ 49 < 7 ^ 161 * r ^ 343 ∧
      ¬ NestedGNAllocationCondition (internalDepthFourSeventhCore p) r) := by
  have hsel := nestedAllocation_branch_selector (internalDepthFourSeventhCore_pos p)
    (Nat.dvd_of_mem_divisors hmem)
  rcases nestedAllocation_threshold_dichotomy (r := r)
    (internalDepthFourSeventhCore_not_seven_dvd p) with h | h
  · exact .inl ⟨h, hsel.1 h⟩
  · exact .inr ⟨h, hsel.2 h⟩

theorem internalDepthFourReconstruction_iff_threshold_routed
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      ThresholdRoutedNestedCondition (internalDepthFourSeventhCore p) := by
  rw [internalDepthFourReconstruction_iff_two_nested_receivers,
    two_nested_receivers_iff_threshold_routed _ (internalDepthFourSeventhCore_pos p)]

/-- Reconstruction has a genuine source-level small-core exclusion. -/
theorem internalDepthFourReconstruction_core_gt_343
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    343 < internalDepthFourSeventhCore p := by
  rcases (internalDepthFourReconstruction_iff_threshold_routed p).mp h with
    ⟨r, hmem, _, _, h⟩
  have hbranch : NestedGNAllocationCondition (internalDepthFourSeventhCore p) r ∨
      NestedRHSAllocationCondition (internalDepthFourSeventhCore p) r :=
    h.elim (fun h => .inl h.2) (fun h => .inr h.2)
  exact (nestedAllocation_coarse_bound (internalDepthFourSeventhCore_pos p)
    (Nat.dvd_of_mem_divisors hmem) hbranch).2.2

theorem internalDepthFourReconstruction_false_of_core_le_343
    (p : RamifiedSignedRootRoutingPacket) (hM : internalDepthFourSeventhCore p ≤ 343) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p := by
  intro h
  have := internalDepthFourReconstruction_core_gt_343 p h
  omega

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The existing seventh-power core split supplies a complementary positive
root. Its exact product with the chosen source core equals the existing
outer root product; no coordinate is identified by depth alone. -/
theorem RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root
    (q : RamifiedRealCubicNormPacket) :
    ∃ N : ℕ, 0 < N ∧
      Int.natAbs (seventhPowerSndCore q.quadratic.innerRoot.fst q.quadratic.innerRoot.snd) =
        N ^ 7 ∧
      Int.natAbs q.innerSndRoot * N =
        q.quadratic.canonical.verticalGapRoot * q.quadratic.compensationRoot ∧
      Nat.Coprime (Int.natAbs q.innerSndRoot) N ∧ ¬ 7 ∣ N := by
  rcases q.quadratic.exists_inner_secondCoordinate_split with ⟨_, N, _, hN⟩
  have hcarrier : Int.natAbs q.quadratic.innerRoot.snd =
      7 ^ 4 * Int.natAbs q.innerSndRoot ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs q.innerSnd_eq
  have hproduct : Int.natAbs q.innerSndRoot * N =
      q.quadratic.canonical.verticalGapRoot * q.quadratic.compensationRoot := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7 ^ 4)
    have h := q.quadratic.inner_secondCoordinate_product_eq
    rw [hcarrier, hN] at h
    simpa only [mul_pow, mul_assoc] using h
  have hNpos : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    have hcore := q.quadratic.innerSndCore_ne_zero
    apply hcore
    apply Int.natAbs_eq_zero.mp
    simpa only [hz, zero_pow (by decide : 7 ≠ 0)] using hN
  have hcop : Nat.Coprime (Int.natAbs q.innerSndRoot) N :=
    q.quadratic.innerRootSnd_innerSndCore_coprime.of_dvd
      (by rw [hcarrier]; exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide)) _)
      (by rw [hN]; exact dvd_pow_self _ (by decide))
  have hNunit : ¬ 7 ∣ N := by
    intro h
    apply q.quadratic.innerSndCore_not_seven_dvd
    apply Int.natCast_dvd.mpr
    rw [hN]
    exact dvd_pow h (by decide : 7 ≠ 0)
  exact ⟨N, hNpos, hN, hproduct, hcop, hNunit⟩

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The reconstruction lower bound restricts the already chosen outer root
product, without inventing an upper bound on the source core. -/
theorem internalDepthFourReconstruction_outer_root_product_gt_343
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    343 <
      p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.canonical.verticalGapRoot *
        p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.compensationRoot := by
  let q := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases q.exists_inner_complementary_seventh_root with ⟨N, hN, _, hproduct, _⟩
  have hM := internalDepthFourReconstruction_core_gt_343 p h
  change 343 < Int.natAbs q.innerSndRoot at hM
  change 343 < q.quadratic.canonical.verticalGapRoot * q.quadratic.compensationRoot
  rw [← hproduct]
  nlinarith

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
