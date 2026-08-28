/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCosineLossBound"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- The cosine loss is globally bounded by one half of the squared angle. -/
theorem abs_cos_sub_one_le_sq_div_two (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have hcos : Real.cos x ≤ 1 := Real.cos_le_one x
  rw [abs_of_nonpos (sub_nonpos.mpr hcos)]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- The adjacent frame angle is bounded using the successor index. -/
theorem abs_etaPairFrameStepPhase_le_two_mul_abs_im_div_succ
    (s : ℂ) (k : ℕ) :
    |etaPairFrameStepPhase s k| ≤
      2 * (|s.im| / (((k + 1 : ℕ) : ℝ))) := by
  rw [abs_etaPairFrameStepPhase]
  exact
    (etaPairFrameStepSpan_le_two_mul_inv s k).trans
      (mul_le_mul_of_nonneg_left
        (abs_im_div_etaPairFrameLeftEndpoint_le_succ s k)
        (by norm_num))

/-- The transported defect partial has the same norm as the original partial. -/
theorem norm_etaCriticalMirrorPairFrameTransportedDefectPartial
    (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorPairFrameTransportedDefectPartial s k‖ =
      ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ := by
  unfold etaCriticalMirrorPairFrameTransportedDefectPartial
  rw [norm_mul, norm_etaPairBaseRotation, one_mul]

/-- Power bound for the transported defect partial at a nonreal zeta zero. -/
theorem norm_etaCriticalMirrorPairFrameTransportedDefectPartial_le
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    ‖etaCriticalMirrorPairFrameTransportedDefectPartial s k‖ ≤
      ‖criticalMirror s‖ *
          (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
            (criticalMirror s).re) +
        ‖s‖ *
          (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re) := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  rw [norm_etaCriticalMirrorPairFrameTransportedDefectPartial]
  rw [etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    hs him (k + 1), norm_neg]
  exact norm_etaCriticalMirrorDefectPairTail_le hsre hmre (by omega)

/-- The signed cosine coefficient carries two reciprocal index powers. -/
theorem abs_etaCriticalMirrorPairedFrameCosineLossCoefficient_le
    (s : ℂ) (k : ℕ) :
    |s.im * (Real.cos (etaPairFrameStepPhase s k) - 1)| ≤
      2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2) := by
  let x : ℝ := (((k + 1 : ℕ) : ℝ))
  let φ : ℝ := etaPairFrameStepPhase s k
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hphase :
      |φ| ≤ 2 * (|s.im| / x) := by
    dsimp [φ, x]
    exact abs_etaPairFrameStepPhase_le_two_mul_abs_im_div_succ s k
  have hphaseSq :
      φ ^ 2 ≤ (2 * (|s.im| / x)) ^ 2 := by
    calc
      φ ^ 2 = |φ| ^ 2 := (sq_abs φ).symm
      _ ≤ (2 * (|s.im| / x)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg φ) hphase 2
  have hcos :
      |Real.cos φ - 1| ≤ φ ^ 2 / 2 :=
    abs_cos_sub_one_le_sq_div_two φ
  have hhalf :
      φ ^ 2 / 2 ≤ (2 * (|s.im| / x)) ^ 2 / 2 := by
    nlinarith
  calc
    |s.im * (Real.cos (etaPairFrameStepPhase s k) - 1)| =
        |s.im| * |Real.cos φ - 1| := by
      dsimp [φ]
      rw [abs_mul]
    _ ≤ |s.im| * (φ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hcos (abs_nonneg s.im)
    _ ≤ |s.im| * ((2 * (|s.im| / x)) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hhalf (abs_nonneg s.im)
    _ = 2 * |s.im| ^ 3 / x ^ 2 := by
      field_simp [hx.ne']
    _ = 2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2) := by
      rfl

/-- Multiplying by two reciprocal powers adds two units to the rpow decay. -/
private theorem inv_sq_mul_rpow_neg_eq_two_extra
    (a : ℝ) (k : ℕ) :
    (1 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) *
        ((((k + 1 : ℕ) : ℝ)) ^ (-a)) =
      (((k + 1 : ℕ) : ℝ)) ^ (-a - 2) := by
  have hx : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  convert (Real.rpow_sub_natCast hx.ne' (-a) 2).symm using 1 <;>
    field_simp; ring_nf

/-- Explicit two-extra-power majorant for one cosine-loss term. -/
noncomputable def etaCriticalMirrorPairedFrameCosineLossMajorant
    (s : ℂ) (k : ℕ) : ℝ :=
  (2 * |s.im| ^ 3 * ‖criticalMirror s‖ /
      (criticalMirror s).re) *
        (((k + 1 : ℕ) : ℝ) ^ (-(criticalMirror s).re - 2)) +
    (2 * |s.im| ^ 3 * ‖s‖ / s.re) *
      (((k + 1 : ℕ) : ℝ) ^ (-s.re - 2))

/-- One cosine-loss term is bounded by the two-extra-power majorant. -/
theorem abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm_le_majorant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    |etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s k| ≤
      etaCriticalMirrorPairedFrameCosineLossMajorant s k := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hcoeff :=
    abs_etaCriticalMirrorPairedFrameCosineLossCoefficient_le s k
  have himNorm :=
    Complex.abs_im_le_norm
      (etaCriticalMirrorPairFrameTransportedDefectPartial s k)
  have hpartial :=
    norm_etaCriticalMirrorPairFrameTransportedDefectPartial_le hs him k
  have hcoefficientNonneg :
      0 ≤ 2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2) := by
    positivity
  have hmirror :=
    inv_sq_mul_rpow_neg_eq_two_extra (criticalMirror s).re k
  have horiginal :=
    inv_sq_mul_rpow_neg_eq_two_extra s.re k
  calc
    |etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s k| =
        |s.im * (Real.cos (etaPairFrameStepPhase s k) - 1)| *
          |(etaCriticalMirrorPairFrameTransportedDefectPartial s k).im| := by
      unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
      rw [abs_mul]
    _ ≤
        (2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) *
          |(etaCriticalMirrorPairFrameTransportedDefectPartial s k).im| :=
      mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    _ ≤
        (2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) *
          ‖etaCriticalMirrorPairFrameTransportedDefectPartial s k‖ :=
      mul_le_mul_of_nonneg_left himNorm hcoefficientNonneg
    _ ≤
        (2 * |s.im| ^ 3 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) *
          (‖criticalMirror s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
                (criticalMirror s).re) +
            ‖s‖ *
              (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re)) :=
      mul_le_mul_of_nonneg_left hpartial hcoefficientNonneg
    _ = etaCriticalMirrorPairedFrameCosineLossMajorant s k := by
      unfold etaCriticalMirrorPairedFrameCosineLossMajorant
      rw [← hmirror, ← horiginal]
      field_simp [hsre.ne', hmre.ne']

/-- A shifted rpow with two extra powers is summable for every positive exponent. -/
private theorem summable_shifted_rpow_two_extra
    {a : ℝ} (ha : 0 < a) :
    Summable
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ (-a - 2))) := by
  have hp : 1 < a + 2 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(a + 2))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hshift := (summable_nat_add_iff 1).2 hbase
  simpa [show -a - 2 = -(a + 2) by ring] using hshift

/-- The cosine-loss majorant is summable throughout the open mirror strip. -/
theorem summable_etaCriticalMirrorPairedFrameCosineLossMajorant
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re) :
    Summable (etaCriticalMirrorPairedFrameCosineLossMajorant s) := by
  unfold etaCriticalMirrorPairedFrameCosineLossMajorant
  exact
    ((summable_shifted_rpow_two_extra hm).mul_left
      (2 * |s.im| ^ 3 * ‖criticalMirror s‖ /
        (criticalMirror s).re)).add
      ((summable_shifted_rpow_two_extra hs).mul_left
        (2 * |s.im| ^ 3 * ‖s‖ / s.re))

/-- The cosine-loss series is absolutely summable at every nonreal zeta zero. -/
theorem summable_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable (etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s) := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  exact
    (summable_etaCriticalMirrorPairedFrameCosineLossMajorant hsre hmre).of_norm_bounded
      (fun k => by
        simpa only [Real.norm_eq_abs] using
          abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm_le_majorant
            hs him k)

/-- Tail of the cosine-loss correction beginning at correction index `K`. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionCosineLossTail
    (K : ℕ) (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s (n + K)

/-- Explicit one-extra-tail-power bound for the cosine-loss tail. -/
noncomputable def etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound
    (s : ℂ) (K : ℕ) : ℝ :=
  (2 * |s.im| ^ 3 * ‖criticalMirror s‖ /
      (criticalMirror s).re) *
        (((K : ℝ) ^ (-(criticalMirror s).re - 1)) /
          ((criticalMirror s).re + 1)) +
    (2 * |s.im| ^ 3 * ‖s‖ / s.re) *
      (((K : ℝ) ^ (-s.re - 1)) / (s.re + 1))

/-- The shifted cosine-loss majorant obeys the explicit tail power bound. -/
theorem tsum_etaCriticalMirrorPairedFrameCosineLossMajorant_nat_add_le_powerBound
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑' n : ℕ,
      etaCriticalMirrorPairedFrameCosineLossMajorant s (n + K)) ≤
      etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
  let A : ℝ :=
    2 * |s.im| ^ 3 * ‖criticalMirror s‖ / (criticalMirror s).re
  let B : ℝ := 2 * |s.im| ^ 3 * ‖s‖ / s.re
  have hMirrorTail :=
    shifted_rpow_tail_le (σ := (criticalMirror s).re + 1)
      (by linarith) hK
  have hOriginalTail :=
    shifted_rpow_tail_le (σ := s.re + 1) (by linarith) hK
  have hMirrorTail' :
      (∑' n : ℕ,
        (((n + K + 1 : ℕ) : ℝ) ^
          (-(criticalMirror s).re - 2))) ≤
        ((K : ℝ) ^ (-(criticalMirror s).re - 1)) /
          ((criticalMirror s).re + 1) := by
    convert hMirrorTail using 1
    · apply tsum_congr
      intro n
      congr 1; ring
    · ring_nf
  have hOriginalTail' :
      (∑' n : ℕ,
        (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) ≤
        ((K : ℝ) ^ (-s.re - 1)) / (s.re + 1) := by
    convert hOriginalTail using 1
    · apply tsum_congr
      intro n
      congr 1; ring
    · ring_nf
  have hMirrorSummable :
      Summable
        (fun n : ℕ =>
          (((n + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 2))) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff K).2
        (summable_shifted_rpow_two_extra hm)
  have hOriginalSummable :
      Summable
        (fun n : ℕ =>
          (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff K).2
        (summable_shifted_rpow_two_extra hs)
  have hMirrorScaled := hMirrorSummable.mul_left A
  have hOriginalScaled := hOriginalSummable.mul_left B
  have hMirrorFactor :
      (∑' n : ℕ,
        A * (((n + K + 1 : ℕ) : ℝ) ^
          (-(criticalMirror s).re - 2))) =
        A * (∑' n : ℕ,
          (((n + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 2))) :=
    (hMirrorSummable.hasSum.mul_left A).tsum_eq
  have hOriginalFactor :
      (∑' n : ℕ,
        B * (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) =
        B * (∑' n : ℕ,
          (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) :=
    (hOriginalSummable.hasSum.mul_left B).tsum_eq
  have hAdd :=
    (hMirrorScaled.hasSum.add hOriginalScaled.hasSum).tsum_eq
  have hmajorantTsum :
      (∑' n : ℕ,
        etaCriticalMirrorPairedFrameCosineLossMajorant s (n + K)) =
        A * (∑' n : ℕ,
          (((n + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 2))) +
        B * (∑' n : ℕ,
          (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) := by
    unfold etaCriticalMirrorPairedFrameCosineLossMajorant
    change
      (∑' n : ℕ,
        (A * (((n + K + 1 : ℕ) : ℝ) ^
            (-(criticalMirror s).re - 2)) +
          B * (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2)))) = _
    rw [hAdd, hMirrorFactor, hOriginalFactor]
  rw [hmajorantTsum]
  unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound
  change
    A * (∑' n : ℕ,
      (((n + K + 1 : ℕ) : ℝ) ^
        (-(criticalMirror s).re - 2))) +
    B * (∑' n : ℕ,
      (((n + K + 1 : ℕ) : ℝ) ^ (-s.re - 2))) ≤
    A * (((K : ℝ) ^ (-(criticalMirror s).re - 1)) /
      ((criticalMirror s).re + 1)) +
    B * (((K : ℝ) ^ (-s.re - 1)) / (s.re + 1))
  exact add_le_add
    (mul_le_mul_of_nonneg_left hMirrorTail'
      (by dsimp [A]; positivity))
    (mul_le_mul_of_nonneg_left hOriginalTail'
      (by dsimp [B]; positivity))

/-- The cosine-loss tail obeys its explicit one-extra-tail-power bound. -/
theorem abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) {K : ℕ} (hK : 1 ≤ K) :
    |etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
      etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hMajorantShift :
      Summable
        (fun n : ℕ =>
          etaCriticalMirrorPairedFrameCosineLossMajorant s (n + K)) :=
    (summable_nat_add_iff K).2
      (summable_etaCriticalMirrorPairedFrameCosineLossMajorant hsre hmre)
  have hnorm :
      |etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
        ∑' n : ℕ,
          etaCriticalMirrorPairedFrameCosineLossMajorant s (n + K) := by
    unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTail
    change
      ‖∑' n : ℕ,
        etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s (n + K)‖ ≤ _
    exact
      tsum_of_norm_bounded hMajorantShift.hasSum
        (fun n => by
          simpa only [Real.norm_eq_abs] using
            abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm_le_majorant
              hs him (n + K))
  exact hnorm.trans
    (tsum_etaCriticalMirrorPairedFrameCosineLossMajorant_nat_add_le_powerBound
      hsre hmre hK)

end DkMath.RH.CFBRCProjection
