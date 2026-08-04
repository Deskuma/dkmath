/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockGeometry
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockCertificate"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/--
An eventual natural-number property holds uniformly after every nonnegative
offset from a sufficiently late block start.
-/
private theorem eventually_all_nat_add_growingBlock
    {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, P (K + j) := by
  rcases eventually_atTop.1 hP with ⟨K₀, hK₀⟩
  exact eventually_atTop.2 ⟨K₀, by
    intro K hK j
    exact hK₀ (K + j) (by omega)⟩

/--
Pure algebraic comparison used uniformly inside a scheduled growing block.
-/
private theorem growingBlockTransferError_lt_margin_of_scaledNorm_le
    {t C S n M : ℝ}
    (ht : t ≠ 0)
    (hS : 0 ≤ S)
    (hM : 0 < M)
    (hscaled : (t ^ 2 / 4) * n ≤ C * M)
    (hangle : 8 * C * S < |t|) :
    2 * |t| * S * n < M := by
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
  have hangleM :
      (8 * C * S) * M < |t| * M :=
    mul_lt_mul_of_pos_right hangle hM
  have hcombined :
      |t| * (2 * |t| * S * n) < |t| * M := by
    calc
      |t| * (2 * |t| * S * n) =
          8 * S * ((|t| ^ 2 / 4) * n) := by ring
      _ ≤ 8 * S * (C * M) := hmul
      _ = (8 * C * S) * M := by ring
      _ < |t| * M := hangleM
  exact (mul_lt_mul_iff_of_pos_left habsPos).mp hcombined

/-- A nonempty finite range of strictly positive real terms has positive sum. -/
private theorem sum_range_pos_of_pos
    (f : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N)
    (hf : ∀ j : ℕ, j < N → 0 < f j) :
    0 < (Finset.range N).sum f := by
  revert hN hf
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hf
      rw [Finset.sum_range_succ]
      by_cases hzero : N = 0
      · subst N
        simpa using hf 0 (by omega)
      · exact
          add_pos
            (ih (Nat.pos_of_ne_zero hzero)
              (fun j hj => hf j (by omega)))
            (hf N (by omega))

/-- A nonempty finite range of strictly negative real terms has negative sum. -/
private theorem sum_range_neg_of_neg
    (f : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N)
    (hf : ∀ j : ℕ, j < N → f j < 0) :
    (Finset.range N).sum f < 0 := by
  revert hN hf
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hf
      rw [Finset.sum_range_succ]
      by_cases hzero : N = 0
      · subst N
        simpa using hf 0 (by omega)
      · exact
          add_neg
            (ih (Nat.pos_of_ne_zero hzero)
              (fun j hj => hf j (by omega)))
            (hf N (by omega))

namespace EtaPairGrowingBlockSchedule

/--
Right of the critical line, every pair in a scheduled growing block is
eventually positive in the single frame chosen at the beginning of that block.
-/
theorem eventually_all_blockStartDefectPairProjection_pos_of_half_lt_re
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        0 < etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  have hspan := S.eventually_all_subblockSpan_le_one s
  have hangle :=
    S.eventually_all_subblock_eight_mul_normCoefficient_mul_span_lt_abs_im
      him
  have hnorm :=
    eventually_all_nat_add_growingBlock
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
        hs hre)
  have hlocal :=
    eventually_all_nat_add_growingBlock
      (eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, hangle, hnorm, hlocal] with
      K hspanK hangleK hnormK hlocalK
  intro j hj
  have hjle : j ≤ S.blockLength K := Nat.le_of_lt hj
  have herror :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRightPairMargin s (K + j) :=
    growingBlockTransferError_lt_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      (etaCriticalMirrorRightPairMargin_pos him (K + j))
      (hnormK j)
      (hangleK j hjle)
  apply
    etaCriticalMirrorBlockStartDefectPairProjection_pos_of_local_margin
      s K j (hspanK j hjle)
  exact herror.trans_le (hlocalK j)

/--
Left of the critical line, every pair in a scheduled growing block is
eventually negative in the same block-start frame.
-/
theorem eventually_all_blockStartDefectPairProjection_neg_of_re_lt_half
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < S.blockLength K →
        etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 := by
  have hspan := S.eventually_all_subblockSpan_le_one s
  have hangle :=
    S.eventually_all_subblock_eight_mul_normCoefficient_mul_span_lt_abs_im
      him
  have hnorm :=
    eventually_all_nat_add_growingBlock
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
        hs hre)
  have hlocal :=
    eventually_all_nat_add_growingBlock
      (eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, hangle, hnorm, hlocal] with
      K hspanK hangleK hnormK hlocalK
  intro j hj
  have hjle : j ≤ S.blockLength K := Nat.le_of_lt hj
  have herror :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorLeftPairMargin s (K + j) :=
    growingBlockTransferError_lt_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      (etaCriticalMirrorLeftPairMargin_pos him (K + j))
      (hnormK j)
      (hangleK j hjle)
  apply
    etaCriticalMirrorBlockStartDefectPairProjection_neg_of_local_margin
      s K j (hspanK j hjle)
  exact herror.trans_le (hlocalK j)

/--
Right of the critical line, the projection of the whole scheduled growing
block is eventually strictly positive in its one block-start frame.
-/
theorem eventually_blockStartDefectBlockProjection_pos_of_half_lt_re
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectBlockProjection
        s K (S.blockLength K) := by
  have hlength := S.eventually_blockLength_pos
  have hall :=
    S.eventually_all_blockStartDefectPairProjection_pos_of_half_lt_re
      hs him hre
  filter_upwards [hlength, hall] with K hlengthK hallK
  rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
  exact
    sum_range_pos_of_pos
      (fun j : ℕ => etaCriticalMirrorBlockStartDefectPairProjection s K j)
      hlengthK hallK

/--
Left of the critical line, the projection of the whole scheduled growing
block is eventually strictly negative in its one block-start frame.
-/
theorem eventually_blockStartDefectBlockProjection_neg_of_re_lt_half
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectBlockProjection
        s K (S.blockLength K) < 0 := by
  have hlength := S.eventually_blockLength_pos
  have hall :=
    S.eventually_all_blockStartDefectPairProjection_neg_of_re_lt_half
      hs him hre
  filter_upwards [hlength, hall] with K hlengthK hallK
  rw [etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum]
  exact
    sum_range_neg_of_neg
      (fun j : ℕ => etaCriticalMirrorBlockStartDefectPairProjection s K j)
      hlengthK hallK

end EtaPairGrowingBlockSchedule

end DkMath.RH.CFBRCProjection
