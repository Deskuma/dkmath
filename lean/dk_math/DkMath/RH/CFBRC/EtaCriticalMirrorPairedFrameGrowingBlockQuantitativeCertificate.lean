/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockCertificate
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- Lift one eventual pair-index statement uniformly beyond every late block start. -/
private theorem eventually_all_nat_add_growingBlockQuantitative
    {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, P (K + j) := by
  rcases eventually_atTop.1 hP with ⟨K₀, hK₀⟩
  exact eventually_atTop.2 ⟨K₀, by
    intro K hK j
    exact hK₀ (K + j) (by omega)⟩

/--
A twice-stronger angular condition retains strictly more than one half of a
positive pair margin after frame transport.
-/
private theorem growingBlockTransferError_lt_half_margin_of_scaledNorm_le
    {t C S n M : ℝ}
    (ht : t ≠ 0)
    (hS : 0 ≤ S)
    (hM : 0 < M)
    (hscaled : (t ^ 2 / 4) * n ≤ C * M)
    (hangle : 16 * C * S < |t|) :
    2 * |t| * S * n < M / 2 := by
  have habsPos : 0 < |t| := abs_pos.mpr ht
  have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hscaled' :
      (|t| ^ 2 / 4) * n ≤ C * M := by
    rw [habsSq]
    exact hscaled
  have hmul :
      8 * S * ((|t| ^ 2 / 4) * n) ≤
        8 * S * (C * M) :=
    mul_le_mul_of_nonneg_left hscaled'
      (mul_nonneg (by norm_num) hS)
  have hhalfPos : 0 < M / 2 := by positivity
  have hangleHalf :
      (16 * C * S) * (M / 2) <
        |t| * (M / 2) :=
    mul_lt_mul_of_pos_right hangle hhalfPos
  have hcombined :
      |t| * (2 * |t| * S * n) <
        |t| * (M / 2) := by
    calc
      |t| * (2 * |t| * S * n) =
          8 * S * ((|t| ^ 2 / 4) * n) := by ring
      _ ≤ 8 * S * (C * M) := hmul
      _ = (16 * C * S) * (M / 2) := by ring
      _ < |t| * (M / 2) := hangleHalf
  exact (mul_lt_mul_iff_of_pos_left habsPos).mp hcombined

/-- Strict pointwise inequalities over a nonempty finite range add strictly. -/
private theorem sum_range_lt_sum_of_lt
    (f g : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N)
    (hfg : ∀ j : ℕ, j < N → f j < g j) :
    (Finset.range N).sum f < (Finset.range N).sum g := by
  revert hN hfg
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hfg
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      by_cases hzero : N = 0
      · subst N
        simpa using hfg 0 (by omega)
      · exact
          add_lt_add
            (ih (Nat.pos_of_ne_zero hzero)
              (fun j hj => hfg j (by omega)))
            (hfg N (by omega))

/-- Sum of the explicit right pair margins over one indexed block. -/
noncomputable def etaCriticalMirrorRightBlockMarginSum
    (s : ℂ) (K N : ℕ) : ℝ :=
  (Finset.range N).sum fun j : ℕ =>
    etaCriticalMirrorRightPairMargin s (K + j)

/-- Sum of the explicit left pair margins over one indexed block. -/
noncomputable def etaCriticalMirrorLeftBlockMarginSum
    (s : ℂ) (K N : ℕ) : ℝ :=
  (Finset.range N).sum fun j : ℕ =>
    etaCriticalMirrorLeftPairMargin s (K + j)

namespace EtaPairGrowingBlockSchedule

/--
The stronger half-margin angular condition eventually holds uniformly on all
initial subblocks of a scheduled growing block.
-/
theorem eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| := by
  have hfull :
      ∀ᶠ K : ℕ in atTop,
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K (S.blockLength K) <
          |s.im| := by
    have hscaled :
        Tendsto
          (fun K : ℕ =>
            16 * etaCriticalMirrorDefectPairNormCoefficient s *
              etaPairFrameBlockSpan s K (S.blockLength K))
          atTop (nhds 0) := by
      simpa [mul_assoc] using
        (S.frameBlockSpan_tendsto_zero s).const_mul
          (16 * etaCriticalMirrorDefectPairNormCoefficient s)
    exact hscaled.eventually_lt_const (abs_pos.mpr him)
  filter_upwards [hfull] with K hK
  intro j hj
  have hmono :
      16 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K j ≤
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K (S.blockLength K) :=
    mul_le_mul_of_nonneg_left
      (etaPairFrameBlockSpan_mono_length s K hj)
      (by
        have hc : 0 ≤ etaCriticalMirrorDefectPairNormCoefficient s :=
          etaCriticalMirrorDefectPairNormCoefficient_nonneg s
        positivity)
  exact hmono.trans_lt hK

/--
Right of the critical line, every pair in the scheduled growing block retains
strictly more than one half of its explicit right margin in the common frame.
-/
theorem eventually_all_rightPairMargin_div_two_lt_blockStartProjection
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorRightPairMargin s (K + j) / 2 <
          etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  have hspan := S.eventually_all_subblockSpan_le_one s
  have hangle :=
    S.eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
      him
  have hnorm :=
    eventually_all_nat_add_growingBlockQuantitative
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
        hs hre)
  have hlocal :=
    eventually_all_nat_add_growingBlockQuantitative
      (eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, hangle, hnorm, hlocal] with
      K hspanK hangleK hnormK hlocalK
  intro j hj
  have hjle : j ≤ S.blockLength K := Nat.le_of_lt hj
  have hMpos :
      0 < etaCriticalMirrorRightPairMargin s (K + j) :=
    etaCriticalMirrorRightPairMargin_pos him (K + j)
  have herror :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRightPairMargin s (K + j) / 2 :=
    growingBlockTransferError_lt_half_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      hMpos
      (hnormK j)
      (hangleK j hjle)
  have habsError :
      |etaCriticalMirrorBlockStartDefectPairProjection s K j -
          etaCriticalMirrorRotatedDefectPairProjection s (K + j)| <
        etaCriticalMirrorRightPairMargin s (K + j) / 2 :=
    lt_of_le_of_lt
      (abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
        s K j (hspanK j hjle))
      herror
  have hlower := neg_lt_of_abs_lt habsError
  have hlocalK := hlocalK j
  linarith

/--
Left of the critical line, every pair retains more than one half of its
explicit left margin after negating the common-frame projection.
-/
theorem eventually_all_leftPairMargin_div_two_lt_neg_blockStartProjection
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorLeftPairMargin s (K + j) / 2 <
          -etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  have hspan := S.eventually_all_subblockSpan_le_one s
  have hangle :=
    S.eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
      him
  have hnorm :=
    eventually_all_nat_add_growingBlockQuantitative
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
        hs hre)
  have hlocal :=
    eventually_all_nat_add_growingBlockQuantitative
      (eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, hangle, hnorm, hlocal] with
      K hspanK hangleK hnormK hlocalK
  intro j hj
  have hjle : j ≤ S.blockLength K := Nat.le_of_lt hj
  have hMpos :
      0 < etaCriticalMirrorLeftPairMargin s (K + j) :=
    etaCriticalMirrorLeftPairMargin_pos him (K + j)
  have herror :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorLeftPairMargin s (K + j) / 2 :=
    growingBlockTransferError_lt_half_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      hMpos
      (hnormK j)
      (hangleK j hjle)
  have habsError :
      |etaCriticalMirrorBlockStartDefectPairProjection s K j -
          etaCriticalMirrorRotatedDefectPairProjection s (K + j)| <
        etaCriticalMirrorLeftPairMargin s (K + j) / 2 :=
    lt_of_le_of_lt
      (abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
        s K j (hspanK j hjle))
      herror
  have hupper := lt_of_abs_lt habsError
  have hlocalK := hlocalK j
  linarith

/--
Right of the critical line, one half of the total explicit right margin is a
strict lower bound for the scheduled common-frame block projection.
-/
theorem eventually_half_rightBlockMarginSum_lt_blockStartProjection
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      (1 : ℝ) / 2 *
          etaCriticalMirrorRightBlockMarginSum s K (S.blockLength K) <
        etaCriticalMirrorBlockStartDefectBlockProjection
          s K (S.blockLength K) := by
  have hlength := S.eventually_blockLength_pos
  have hall :=
    S.eventually_all_rightPairMargin_div_two_lt_blockStartProjection
      hs him hre
  filter_upwards [hlength, hall] with K hlengthK hallK
  rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
  unfold etaCriticalMirrorRightBlockMarginSum
  calc
    (1 : ℝ) / 2 *
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ => etaCriticalMirrorRightPairMargin s (K + j)) =
      (Finset.range (S.blockLength K)).sum
        (fun j : ℕ =>
          (1 : ℝ) / 2 * etaCriticalMirrorRightPairMargin s (K + j)) := by
      rw [Finset.mul_sum]
    _ <
      (Finset.range (S.blockLength K)).sum
        (fun j : ℕ =>
          etaCriticalMirrorBlockStartDefectPairProjection s K j) := by
      apply sum_range_lt_sum_of_lt
      · exact hlengthK
      · intro j hj
        convert hallK j hj using 1
        ring

/--
Left of the critical line, one half of the total explicit left margin is a
strict lower bound for the negated scheduled common-frame block projection.
-/
theorem eventually_half_leftBlockMarginSum_lt_neg_blockStartProjection
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      (1 : ℝ) / 2 *
          etaCriticalMirrorLeftBlockMarginSum s K (S.blockLength K) <
        -etaCriticalMirrorBlockStartDefectBlockProjection
          s K (S.blockLength K) := by
  have hlength := S.eventually_blockLength_pos
  have hall :=
    S.eventually_all_leftPairMargin_div_two_lt_neg_blockStartProjection
      hs him hre
  filter_upwards [hlength, hall] with K hlengthK hallK
  rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
  unfold etaCriticalMirrorLeftBlockMarginSum
  calc
    (1 : ℝ) / 2 *
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ => etaCriticalMirrorLeftPairMargin s (K + j)) =
      (Finset.range (S.blockLength K)).sum
        (fun j : ℕ =>
          (1 : ℝ) / 2 * etaCriticalMirrorLeftPairMargin s (K + j)) := by
      rw [Finset.mul_sum]
    _ <
      (Finset.range (S.blockLength K)).sum
        (fun j : ℕ =>
          -etaCriticalMirrorBlockStartDefectPairProjection s K j) := by
      apply sum_range_lt_sum_of_lt
      · exact hlengthK
      · intro j hj
        convert hallK j hj using 1
        ring
    _ =
      -(Finset.range (S.blockLength K)).sum
        (fun j : ℕ =>
          etaCriticalMirrorBlockStartDefectPairProjection s K j) := by
      simp

end EtaPairGrowingBlockSchedule

end DkMath.RH.CFBRCProjection
