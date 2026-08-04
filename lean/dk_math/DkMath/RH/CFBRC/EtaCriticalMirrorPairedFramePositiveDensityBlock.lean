/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingProjectionTailMargin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityBlock"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- Lift one eventual pair-index statement uniformly beyond every late start. -/
private theorem eventually_all_nat_add_positiveDensityBlock
    {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, P (K + j) := by
  rcases eventually_atTop.1 hP with ⟨K₀, hK₀⟩
  exact eventually_atTop.2 ⟨K₀, by
    intro K hK j
    exact hK₀ (K + j) (by omega)⟩

/--
A block schedule whose length has a strictly positive asymptotic ratio to the
pair-left endpoint `2K+1`.
-/
structure EtaPairPositiveDensityBlockSchedule where
  blockLength : ℕ → ℕ
  density : ℝ
  density_pos : 0 < density
  blockLength_tendsto_atTop : Tendsto blockLength atTop atTop
  relativeLength_tendsto_density :
    Tendsto
      (fun K : ℕ =>
        (blockLength K : ℝ) / etaPairFrameLeftEndpoint K)
      atTop (nhds density)

/-- The canonical linear schedule `N(K)=K`, whose relative density is `1/2`. -/
def etaPairHalfDensityBlockSchedule :
    EtaPairPositiveDensityBlockSchedule where
  blockLength := fun K : ℕ => K
  density := (1 : ℝ) / 2
  density_pos := by norm_num
  blockLength_tendsto_atTop := tendsto_id
  relativeLength_tendsto_density := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) 0 1 1 (d := 2) (by norm_num)
    simpa [etaPairFrameLeftEndpoint, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using h

@[simp]
theorem etaPairHalfDensityBlockSchedule_blockLength
    (K : ℕ) :
    etaPairHalfDensityBlockSchedule.blockLength K = K :=
  rfl

@[simp]
theorem etaPairHalfDensityBlockSchedule_density :
    etaPairHalfDensityBlockSchedule.density = (1 : ℝ) / 2 :=
  rfl

namespace EtaPairPositiveDensityBlockSchedule

/-- Every positive-density schedule is eventually nonempty. -/
theorem eventually_blockLength_pos
    (S : EtaPairPositiveDensityBlockSchedule) :
    ∀ᶠ K : ℕ in atTop, 0 < S.blockLength K := by
  have hge : ∀ᶠ K : ℕ in atTop, 1 ≤ S.blockLength K :=
    (tendsto_atTop.1 S.blockLength_tendsto_atTop) 1
  filter_upwards [hge] with K hK
  omega

/--
Any strict upper bound above the limiting frame-span majorant eventually
bounds the complete scheduled block span.
-/
theorem eventually_frameBlockSpan_lt_of_density_upper
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) {A : ℝ}
    (hA : 2 * |s.im| * S.density < A) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K (S.blockLength K) < A := by
  have hupper :
      Tendsto
        (fun K : ℕ =>
          2 * |s.im| *
            ((S.blockLength K : ℝ) /
              etaPairFrameLeftEndpoint K))
        atTop
        (nhds (2 * |s.im| * S.density)) := by
    simpa [mul_assoc] using
      S.relativeLength_tendsto_density.const_mul (2 * |s.im|)
  filter_upwards [hupper.eventually_lt_const hA] with K hK
  exact
    (etaPairFrameBlockSpan_le_two_mul_abs_im_mul_relativeLength
      s K (S.blockLength K)).trans_lt hK

/-- The same density upper bound controls every initial subblock uniformly. -/
theorem eventually_all_subblockSpan_lt_of_density_upper
    (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) {A : ℝ}
    (hA : 2 * |s.im| * S.density < A) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        etaPairFrameBlockSpan s K j < A := by
  filter_upwards [S.eventually_frameBlockSpan_lt_of_density_upper s hA]
      with K hK
  intro j hj
  exact (etaPairFrameBlockSpan_mono_length s K hj).trans_lt hK

/--
Optional admissibility condition ensuring that every scheduled subblock obeys
the half-margin angular estimate used by the common-frame argument.
-/
def SmallAngleAdmissible
    (S : EtaPairPositiveDensityBlockSchedule) (s : ℂ) : Prop :=
  32 * etaCriticalMirrorDefectPairNormCoefficient s * S.density < 1

/-- A small admissible positive density gives the uniform sixteen-fold angle bound. -/
theorem eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0)
    (hsmall : S.SmallAngleAdmissible s) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| := by
  have habs : 0 < |s.im| := abs_pos.mpr him
  have hlimit :
      32 * etaCriticalMirrorDefectPairNormCoefficient s *
          |s.im| * S.density <
        |s.im| := by
    calc
      32 * etaCriticalMirrorDefectPairNormCoefficient s *
          |s.im| * S.density =
        (32 * etaCriticalMirrorDefectPairNormCoefficient s *
          S.density) * |s.im| := by ring
      _ < 1 * |s.im| :=
        mul_lt_mul_of_pos_right hsmall habs
      _ = |s.im| := one_mul _
  have hscaled :
      Tendsto
        (fun K : ℕ =>
          32 * etaCriticalMirrorDefectPairNormCoefficient s *
            |s.im| *
              ((S.blockLength K : ℝ) /
                etaPairFrameLeftEndpoint K))
        atTop
        (nhds
          (32 * etaCriticalMirrorDefectPairNormCoefficient s *
            |s.im| * S.density)) := by
    simpa [mul_assoc] using
      S.relativeLength_tendsto_density.const_mul
        (32 * etaCriticalMirrorDefectPairNormCoefficient s * |s.im|)
  filter_upwards [hscaled.eventually_lt_const hlimit] with K hK
  intro j hj
  calc
    16 * etaCriticalMirrorDefectPairNormCoefficient s *
        etaPairFrameBlockSpan s K j ≤
      16 * etaCriticalMirrorDefectPairNormCoefficient s *
        (2 * |s.im| *
          ((j : ℝ) / etaPairFrameLeftEndpoint K)) := by
      exact mul_le_mul_of_nonneg_left
        (etaPairFrameBlockSpan_le_two_mul_abs_im_mul_relativeLength
          s K j)
        (by
          have hc :
              0 ≤ etaCriticalMirrorDefectPairNormCoefficient s :=
            etaCriticalMirrorDefectPairNormCoefficient_nonneg s
          positivity)
    _ ≤
      16 * etaCriticalMirrorDefectPairNormCoefficient s *
        (2 * |s.im| *
          ((S.blockLength K : ℝ) /
            etaPairFrameLeftEndpoint K)) := by
      have hleft : 0 < etaPairFrameLeftEndpoint K :=
        etaPairFrameLeftEndpoint_pos K
      gcongr
      exact_mod_cast hj
    _ =
      32 * etaCriticalMirrorDefectPairNormCoefficient s *
        |s.im| *
          ((S.blockLength K : ℝ) /
            etaPairFrameLeftEndpoint K) := by ring
    _ < |s.im| := hK

/--
Right of the critical line, every positive-density block margin is eventually
a strict lower bound for the complete moving projection tail.
-/
theorem eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRightBlockMarginSum
          s K (S.blockLength K) <
        etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hlocal :=
    eventually_all_nat_add_positiveDensityBlock
      (eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
        hs him hre)
  have htail :=
    eventually_all_nat_add_positiveDensityBlock
      (eventually_etaCriticalMirrorRotatedDefectProjectionTail_pos_of_half_lt_re
        hs him hre)
  filter_upwards [hlocal, htail] with K hlocalK htailK
  rw [etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    hs K (S.blockLength K)]
  unfold etaCriticalMirrorRightBlockMarginSum
  have hsum :
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRightPairMargin s (K + j)) ≤
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hlocalK j
  linarith [htailK (S.blockLength K)]

/--
Left of the critical line, every positive-density block margin is eventually
a strict lower bound for the negated moving projection tail.
-/
theorem eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorLeftBlockMarginSum
          s K (S.blockLength K) <
        -etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hlocal :=
    eventually_all_nat_add_positiveDensityBlock
      (eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
        hs him hre)
  have htail :=
    eventually_all_nat_add_positiveDensityBlock
      (eventually_etaCriticalMirrorRotatedDefectProjectionTail_neg_of_re_lt_half
        hs him hre)
  filter_upwards [hlocal, htail] with K hlocalK htailK
  rw [etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    hs K (S.blockLength K)]
  unfold etaCriticalMirrorLeftBlockMarginSum
  have hsum :
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorLeftPairMargin s (K + j)) ≤
        -(Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
    calc
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorLeftPairMargin s (K + j)) ≤
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            -etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlocalK j
      _ =
        -(Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
        simp
  linarith [htailK (S.blockLength K)]

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
