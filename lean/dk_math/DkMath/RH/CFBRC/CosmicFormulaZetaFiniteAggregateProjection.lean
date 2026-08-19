/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaMirrorGapBeamProjection
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection"

/-!
# CFZP-003: finite canonical prime-power mirror aggregate

This module aggregates the source-derived mirror square mass, its CF2D
interaction body, and its mirror-offset Gap over the canonical finite
prime-power support.  The same canonical shadow cost is used in all three
finite ledgers.

The aggregate Gap is also factored through the CFZP-002 analytic Gap Beam.
This remains a finite positive-amplitude construction: it does not identify
the ledger with a signed PHZ sum, a Mellin source, a rectangle identity, or a
zeta zero statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.CosmicFormula.ThreeElement
open DkMath.CosmicFormula.Rotation.CF2D

/-! ## Canonical support and weight gates -/

theorem one_lt_of_mem_canonicalPrimePowerSupportUpTo
    {X q : ℕ}
    (hq : q ∈ canonicalPrimePowerSupportUpTo X) :
    1 < q := by
  have hlabel := (mem_canonicalPrimePowerSupportUpTo_iff.mp hq).2
  rcases primePowerShadow_spec hlabel with ⟨hp, hj, hqpow⟩
  rw [hqpow]
  have hjle : 1 ≤ primePowerExponentShadow q := hj
  have hpow : primePowerExponentShadow q <
      primePowerBaseShadow q ^ primePowerExponentShadow q :=
    Nat.lt_pow_self hp.one_lt
  omega

theorem canonicalPrimePowerShadowCost_pos_of_mem
    {X q : ℕ}
    (hq : q ∈ canonicalPrimePowerSupportUpTo X) :
    0 < canonicalPrimePowerShadowCost q := by
  have hlabel := (mem_canonicalPrimePowerSupportUpTo_iff.mp hq).2
  rcases primePowerShadow_spec hlabel with ⟨hp, hj, hqpow⟩
  rw [canonicalPrimePowerShadowCost_eq_log_of_witness
    hp hj hqpow]
  apply Real.log_pos
  exact_mod_cast hp.one_lt

theorem two_mem_canonicalPrimePowerSupportUpTo
    {X : ℕ} (hX : 2 ≤ X) :
    2 ∈ canonicalPrimePowerSupportUpTo X := by
  apply mem_canonicalPrimePowerSupportUpTo_iff.mpr
  refine ⟨hX, ?_⟩
  exact ⟨2, 1, Nat.prime_two, by norm_num, by norm_num⟩

theorem canonicalPrimePowerSupportUpTo_nonempty
    {X : ℕ} (hX : 2 ≤ X) :
    (canonicalPrimePowerSupportUpTo X).Nonempty := by
  exact ⟨2, two_mem_canonicalPrimePowerSupportUpTo hX⟩

/-! ## Finite aggregate definitions -/

/-- The source-derived finite mirror square-mass ledger. -/
noncomputable def cfzpAggregateMirrorBigUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      squareMass
        (primeMirrorOffsetState q δ).core
        (primeMirrorOffsetState q δ).beam

/-- The finite CF2D interaction-body ledger. -/
noncomputable def cfzpAggregateMirrorBodyUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dInteractionBeam (primeMirrorOffsetState q δ)

/-- The finite weighted mirror-offset Gap ledger. -/
noncomputable def cfzpAggregateMirrorGapUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      primeMirrorOffsetGap q δ

/-- The finite analytic Gap-Beam ledger from CFZP-002. -/
noncomputable def cfzpAggregateMirrorGapBeamUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cfzpMirrorGapBeam q δ

/-- The total canonical shadow cost in a finite prime-power support. -/
noncomputable def cfzpAggregateMirrorWeightUpTo (X : ℕ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q

/-! ## Generic finite-energy bridge and completion -/

theorem cfzpAggregateMirrorGapUpTo_eq_primeMirrorEnergy
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ =
      primeMirrorEnergy
        (canonicalPrimePowerSupportUpTo X)
        canonicalPrimePowerShadowCost
        δ := by
  rfl

theorem cfzpAggregateMirrorBigUpTo_eq_body_add_gap
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorBigUpTo X δ =
      cfzpAggregateMirrorBodyUpTo X δ +
        cfzpAggregateMirrorGapUpTo X δ := by
  unfold cfzpAggregateMirrorBigUpTo
    cfzpAggregateMirrorBodyUpTo cfzpAggregateMirrorGapUpTo
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q *
          squareMass
            (primeMirrorOffsetState q δ).core
            (primeMirrorOffsetState q δ).beam) =
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            (cf2dInteractionBeam (primeMirrorOffsetState q δ) +
              primeMirrorOffsetGap q δ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [primeMirrorOffsetState_squareMass_eq_two_add_gap,
        primeMirrorOffsetState_interaction_eq_two]
    _ = ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          (canonicalPrimePowerShadowCost q *
              cf2dInteractionBeam (primeMirrorOffsetState q δ) +
            canonicalPrimePowerShadowCost q * primeMirrorOffsetGap q δ) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            cf2dInteractionBeam (primeMirrorOffsetState q δ)) +
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q * primeMirrorOffsetGap q δ := by
      rw [Finset.sum_add_distrib]

theorem cfzpAggregateMirrorBodyUpTo_eq_two_mul_weight
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorBodyUpTo X δ =
      2 * cfzpAggregateMirrorWeightUpTo X := by
  unfold cfzpAggregateMirrorBodyUpTo cfzpAggregateMirrorWeightUpTo
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q *
          cf2dInteractionBeam (primeMirrorOffsetState q δ)) =
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q * 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [primeMirrorOffsetState_interaction_eq_two]
    _ = ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          2 * canonicalPrimePowerShadowCost q := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = 2 * ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q := by
      rw [Finset.mul_sum]

theorem cfzpAggregateMirrorGapUpTo_nonneg
    (X : ℕ) (δ : ℝ) :
    0 ≤ cfzpAggregateMirrorGapUpTo X δ := by
  rw [cfzpAggregateMirrorGapUpTo_eq_primeMirrorEnergy]
  apply primeMirrorEnergy_nonneg
  intro q hq
  exact (canonicalPrimePowerShadowCost_pos_of_mem hq).le

/--
The finite canonical aggregate detects the horizontal offset exactly, but this
is only an intrinsic source-side statement.  No zeta-zero hypothesis makes
the aggregate vanish here.
-/
theorem cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ = 0 ↔ δ = 0 := by
  rw [cfzpAggregateMirrorGapUpTo_eq_primeMirrorEnergy]
  apply primeMirrorEnergy_eq_zero_iff_delta_eq_zero
  · exact canonicalPrimePowerSupportUpTo_nonempty hX
  · intro q hq
    exact one_lt_of_mem_canonicalPrimePowerSupportUpTo hq
  · intro q hq
    exact canonicalPrimePowerShadowCost_pos_of_mem hq

/-! ## Positivity of the finite ledgers -/

theorem cfzpAggregateMirrorBodyUpTo_pos
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    0 < cfzpAggregateMirrorBodyUpTo X δ := by
  unfold cfzpAggregateMirrorBodyUpTo
  have h2mem : 2 ∈ canonicalPrimePowerSupportUpTo X :=
    two_mem_canonicalPrimePowerSupportUpTo hX
  have h2term :
      0 < canonicalPrimePowerShadowCost 2 *
        cf2dInteractionBeam (primeMirrorOffsetState 2 δ) := by
    rw [primeMirrorOffsetState_interaction_eq_two]
    exact mul_pos
      (canonicalPrimePowerShadowCost_pos_of_mem h2mem)
      (by norm_num)
  have hnonneg : ∀ q ∈ canonicalPrimePowerSupportUpTo X,
      0 ≤ canonicalPrimePowerShadowCost q *
        cf2dInteractionBeam (primeMirrorOffsetState q δ) := by
    intro q hq
    rw [primeMirrorOffsetState_interaction_eq_two]
    exact mul_nonneg
      (canonicalPrimePowerShadowCost_pos_of_mem hq).le
      (by norm_num)
  have hle :
      canonicalPrimePowerShadowCost 2 *
          cf2dInteractionBeam (primeMirrorOffsetState 2 δ) ≤
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            cf2dInteractionBeam (primeMirrorOffsetState q δ) :=
    Finset.single_le_sum (s := canonicalPrimePowerSupportUpTo X)
      (f := fun q : ℕ => canonicalPrimePowerShadowCost q *
        cf2dInteractionBeam (primeMirrorOffsetState q δ)) hnonneg h2mem
  exact lt_of_lt_of_le h2term hle

theorem cfzpAggregateMirrorBigUpTo_pos
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    0 < cfzpAggregateMirrorBigUpTo X δ := by
  rw [cfzpAggregateMirrorBigUpTo_eq_body_add_gap]
  have hbody : 0 < cfzpAggregateMirrorBodyUpTo X δ :=
    cfzpAggregateMirrorBodyUpTo_pos hX δ
  have hgap : 0 ≤ cfzpAggregateMirrorGapUpTo X δ :=
    cfzpAggregateMirrorGapUpTo_nonneg X δ
  linarith

/-! ## Aggregate coordinate factorization -/

/--
The finite source-side mirror Gap factors through the square of the centered
coordinate and a finite nonnegative Gap-Beam coefficient.  This identity is
not a quantitative zero-to-prime estimate: it supplies no bound on `δ` until
an independent theorem controls the left-hand finite aggregate.
-/
theorem cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ =
      δ ^ 2 * cfzpAggregateMirrorGapBeamUpTo X δ := by
  unfold cfzpAggregateMirrorGapUpTo cfzpAggregateMirrorGapBeamUpTo
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
        canonicalPrimePowerShadowCost q * primeMirrorOffsetGap q δ) =
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q *
            (δ ^ 2 * cfzpMirrorGapBeam q δ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam]
    _ = ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          δ ^ 2 *
            (canonicalPrimePowerShadowCost q * cfzpMirrorGapBeam q δ) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = δ ^ 2 * ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q * cfzpMirrorGapBeam q δ := by
      rw [Finset.mul_sum]

theorem cfzpAggregateMirrorGapBeamUpTo_zero_pos
    {X : ℕ} (hX : 2 ≤ X) :
    0 < cfzpAggregateMirrorGapBeamUpTo X 0 := by
  unfold cfzpAggregateMirrorGapBeamUpTo
  have h2mem : 2 ∈ canonicalPrimePowerSupportUpTo X :=
    two_mem_canonicalPrimePowerSupportUpTo hX
  have h2term :
      0 < canonicalPrimePowerShadowCost 2 * cfzpMirrorGapBeam 2 0 :=
    mul_pos
      (canonicalPrimePowerShadowCost_pos_of_mem h2mem)
      (cfzpMirrorGapBeam_zero_pos (by norm_num))
  have hnonneg : ∀ q ∈ canonicalPrimePowerSupportUpTo X,
      0 ≤ canonicalPrimePowerShadowCost q * cfzpMirrorGapBeam q 0 := by
    intro q hq
    exact mul_nonneg
      (canonicalPrimePowerShadowCost_pos_of_mem hq).le
      (by simpa [cfzpMirrorGapBeam] using
        (sq_nonneg (cfzpMirrorAmplitudeDifferenceBeam q 0)))
  have hle :
      canonicalPrimePowerShadowCost 2 * cfzpMirrorGapBeam 2 0 ≤
        ∑ q ∈ canonicalPrimePowerSupportUpTo X,
          canonicalPrimePowerShadowCost q * cfzpMirrorGapBeam q 0 :=
    Finset.single_le_sum (s := canonicalPrimePowerSupportUpTo X)
      (f := fun q : ℕ => canonicalPrimePowerShadowCost q *
        cfzpMirrorGapBeam q 0) hnonneg h2mem
  exact lt_of_lt_of_le h2term hle

end DkMath.RH.CFBRCProjection
