/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportSignAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedDefectTailSplit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Tail of the ordinary paired eta series beginning at pair index `K`. -/
noncomputable def etaPairTail
    (K : ℕ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, etaPairTerm z (j + K)

/-- Every ordinary paired eta tail is summable on the open right half-plane. -/
theorem summable_etaPairTail
    {z : ℂ} (hz : 0 < z.re) (K : ℕ) :
    Summable (fun j : ℕ => etaPairTerm z (j + K)) :=
  (summable_nat_add_iff K).2
    (etaPairedSummableAt_of_pos_re hz)

/-- Shifted one-extra-power sequence used by a single paired eta tail. -/
private theorem summable_shifted_etaPair_power
    {a : ℝ} (ha : 0 < a) (K : ℕ) :
    Summable
      (fun j : ℕ =>
        (((j + K + 1 : ℕ) : ℝ) ^ (-a - 1))) := by
  have hp : 1 < a + 1 := by linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(a + 1))) := by
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_one_div_nat_rpow.2 hp)
  have hshift := (summable_nat_add_iff (K + 1)).2 hbase
  simpa [Nat.add_assoc, show -a - 1 = -(a + 1) by ring] using hshift

/-- Explicit power bound for one ordinary paired eta tail. -/
theorem norm_etaPairTail_le
    {z : ℂ} (hz : 0 < z.re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairTail K z‖ ≤
      ‖z‖ * (((K : ℝ) ^ (-z.re)) / z.re) := by
  have hpow := summable_shifted_etaPair_power hz K
  have hmajorant := hpow.mul_left ‖z‖
  have hnorm :
      ‖etaPairTail K z‖ ≤
        ∑' j : ℕ,
          ‖z‖ *
            (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 1)) := by
    unfold etaPairTail
    exact
      tsum_of_norm_bounded hmajorant.hasSum
        (fun j => by
          simpa [Nat.add_assoc] using
            norm_etaPairTerm_le_summableMajorant hz (j + K))
  have hfactor :
      (∑' j : ℕ,
        ‖z‖ * (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 1))) =
        ‖z‖ *
          (∑' j : ℕ,
            (((j + K + 1 : ℕ) : ℝ) ^ (-z.re - 1))) :=
    (hpow.hasSum.mul_left ‖z‖).tsum_eq
  rw [hfactor] at hnorm
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left
      (shifted_rpow_tail_le hz hK)
      (norm_nonneg z))

/-- The defect tail is exactly mirror paired tail minus original paired tail. -/
theorem etaCriticalMirrorDefectPairTail_eq_etaPairTail_sub
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    (K : ℕ) :
    etaCriticalMirrorDefectPairTail K s =
      etaPairTail K (criticalMirror s) - etaPairTail K s := by
  have hmirror := summable_etaPairTail hm K
  have horiginal := summable_etaPairTail hs K
  unfold etaCriticalMirrorDefectPairTail etaPairTail
  calc
    (∑' j : ℕ,
      etaCriticalMirrorDefectPairTerm s (j + K)) =
        ∑' j : ℕ,
          (etaPairTerm (criticalMirror s) (j + K) -
            etaPairTerm s (j + K)) := by
      apply tsum_congr
      intro j
      exact etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub s (j + K)
    _ =
        (∑' j : ℕ, etaPairTerm (criticalMirror s) (j + K)) -
          ∑' j : ℕ, etaPairTerm s (j + K) :=
      (hmirror.hasSum.sub horiginal.hasSum).tsum_eq

/-- Mirror paired tail transported into the current pair-left frame. -/
noncomputable def etaCriticalMirrorPairFrameRotatedMirrorTail
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k *
    etaPairTail (k + 1) (criticalMirror s)

/-- Original paired tail transported into the current pair-left frame. -/
noncomputable def etaCriticalMirrorPairFrameRotatedOriginalTail
    (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k * etaPairTail (k + 1) s

/-- Exact complex split of the rotated defect tail into mirror minus original. -/
theorem etaCriticalMirrorPairFrameRotatedDefectTail_eq_mirror_sub_original
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedDefectTail s k =
      etaCriticalMirrorPairFrameRotatedMirrorTail s k -
        etaCriticalMirrorPairFrameRotatedOriginalTail s k := by
  unfold etaCriticalMirrorPairFrameRotatedDefectTail
  unfold etaCriticalMirrorPairFrameRotatedMirrorTail
  unfold etaCriticalMirrorPairFrameRotatedOriginalTail
  rw [etaCriticalMirrorDefectPairTail_eq_etaPairTail_sub
    (nontrivialRiemannZetaZero_re_pos hs)
    (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)]
  ring

/-- Real-part split of the rotated defect tail. -/
theorem etaCriticalMirrorPairFrameRotatedDefectTail_re_eq_mirror_sub_original
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    (etaCriticalMirrorPairFrameRotatedDefectTail s k).re =
      (etaCriticalMirrorPairFrameRotatedMirrorTail s k).re -
        (etaCriticalMirrorPairFrameRotatedOriginalTail s k).re := by
  rw [etaCriticalMirrorPairFrameRotatedDefectTail_eq_mirror_sub_original hs k]
  simp

/-- Rotation preserves the norm of the mirror paired tail. -/
theorem norm_etaCriticalMirrorPairFrameRotatedMirrorTail
    (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖ =
      ‖etaPairTail (k + 1) (criticalMirror s)‖ := by
  unfold etaCriticalMirrorPairFrameRotatedMirrorTail
  rw [norm_mul, norm_etaPairBaseRotation, one_mul]

/-- Rotation preserves the norm of the original paired tail. -/
theorem norm_etaCriticalMirrorPairFrameRotatedOriginalTail
    (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖ =
      ‖etaPairTail (k + 1) s‖ := by
  unfold etaCriticalMirrorPairFrameRotatedOriginalTail
  rw [norm_mul, norm_etaPairBaseRotation, one_mul]

/-- Mirror component power bound in the current pair-left frame. -/
theorem norm_etaCriticalMirrorPairFrameRotatedMirrorTail_le
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖ ≤
      ‖criticalMirror s‖ *
        (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
          (criticalMirror s).re) := by
  rw [norm_etaCriticalMirrorPairFrameRotatedMirrorTail]
  exact norm_etaPairTail_le
    (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
    (by omega)

/-- Original component power bound in the current pair-left frame. -/
theorem norm_etaCriticalMirrorPairFrameRotatedOriginalTail_le
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖ ≤
      ‖s‖ *
        (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re) := by
  rw [norm_etaCriticalMirrorPairFrameRotatedOriginalTail]
  exact norm_etaPairTail_le
    (nontrivialRiemannZetaZero_re_pos hs)
    (by omega)

/-- Cofinality of a fixed natural successor shift. -/
private theorem tendsto_nat_add_const_atTop
    (N : ℕ) :
    Tendsto (fun K : ℕ => K + N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro n
  exact eventually_atTop.2 ⟨n, by
    intro K hK
    omega⟩

/-- Right-side successor-index audit for the subordinate original tail. -/
noncomputable def etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit
    (s : ℂ) (k : ℕ) : ℝ :=
  (‖s‖ / s.re) *
    (((k + 1 : ℕ) : ℝ) ^
      (-(s.re - (criticalMirror s).re)))

/-- Left-side successor-index audit for the subordinate mirror tail. -/
noncomputable def etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit
    (s : ℂ) (k : ℕ) : ℝ :=
  (‖criticalMirror s‖ / (criticalMirror s).re) *
    (((k + 1 : ℕ) : ℝ) ^
      (-((criticalMirror s).re - s.re)))

/-- On the right, the normalized original component is bounded by its exponent-gap audit. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedOriginalTail_le_audit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
        ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖ ≤
      etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit s k := by
  have hsre : 0 < s.re :=
    nontrivialRiemannZetaZero_re_pos hs
  have hx : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have htail :=
    norm_etaCriticalMirrorPairFrameRotatedOriginalTail_le hs k
  have hscaleNonneg :
      0 ≤ (((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re :=
    (Real.rpow_pos_of_pos hx _).le
  have hpow :
      ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) =
        (((k + 1 : ℕ) : ℝ)) ^
          (-(s.re - (criticalMirror s).re)) := by
    calc
      ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) =
        (((k + 1 : ℕ) : ℝ)) ^
          ((criticalMirror s).re + (-s.re)) :=
            (Real.rpow_add hx _ _).symm
      _ = (((k + 1 : ℕ) : ℝ)) ^
          (-(s.re - (criticalMirror s).re)) := by
        congr 1
        ring
  calc
    ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
        ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖ ≤
      ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
        (‖s‖ *
          (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re)) :=
      mul_le_mul_of_nonneg_left htail hscaleNonneg
    _ = etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit s k := by
      unfold etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit
      rw [← hpow]
      field_simp [hsre.ne']

/-- On the left, the normalized mirror component is bounded by its exponent-gap audit. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTail_le_audit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
        ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖ ≤
      etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit s k := by
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  have hx : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have htail :=
    norm_etaCriticalMirrorPairFrameRotatedMirrorTail_le hs k
  have hscaleNonneg :
      0 ≤ (((k + 1 : ℕ) : ℝ)) ^ s.re :=
    (Real.rpow_pos_of_pos hx _).le
  have hpow :
      ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) =
        (((k + 1 : ℕ) : ℝ)) ^
          (-((criticalMirror s).re - s.re)) := by
    calc
      ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) =
        (((k + 1 : ℕ) : ℝ)) ^
          (s.re + (-(criticalMirror s).re)) :=
            (Real.rpow_add hx _ _).symm
      _ = (((k + 1 : ℕ) : ℝ)) ^
          (-((criticalMirror s).re - s.re)) := by
        congr 1
        ring
  calc
    ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
        ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖ ≤
      ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
        (‖criticalMirror s‖ *
          (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
            (criticalMirror s).re)) :=
      mul_le_mul_of_nonneg_left htail hscaleNonneg
    _ = etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit s k := by
      unfold etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit
      rw [← hpow]
      field_simp [hmre.ne']

/-- On the right, the subordinate original-tail audit tends to zero. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit_tendsto_zero
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit s)
      atTop (nhds 0) := by
  have hgap : 0 < s.re - (criticalMirror s).re := by
    rw [criticalMirror_re]
    linarith
  have hbase :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) ^ (-(s.re - (criticalMirror s).re))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp
      tendsto_natCast_atTop_atTop
  have hshift := hbase.comp (tendsto_nat_add_const_atTop 1)
  change Tendsto
    (fun k : ℕ =>
      (‖s‖ / s.re) *
        (((k + 1 : ℕ) : ℝ) ^
          (-(s.re - (criticalMirror s).re))))
    atTop _
  simpa [Function.comp_def] using
    tendsto_const_nhds.mul hshift

/-- On the left, the subordinate mirror-tail audit tends to zero. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit_tendsto_zero
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit s)
      atTop (nhds 0) := by
  have hgap : 0 < (criticalMirror s).re - s.re := by
    rw [criticalMirror_re]
    linarith
  have hbase :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) ^ (-((criticalMirror s).re - s.re))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp
      tendsto_natCast_atTop_atTop
  have hshift := hbase.comp (tendsto_nat_add_const_atTop 1)
  change Tendsto
    (fun k : ℕ =>
      (‖criticalMirror s‖ / (criticalMirror s).re) *
        (((k + 1 : ℕ) : ℝ) ^
          (-((criticalMirror s).re - s.re))))
    atTop _
  simpa [Function.comp_def] using
    tendsto_const_nhds.mul hshift

/-- On the right, the successor-index normalized original rotated tail vanishes. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedOriginalTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖)
      atTop (nhds 0) := by
  have hupper :=
    etaCriticalMirrorRightIndexNormalizedRotatedOriginalTailPowerAudit_tendsto_zero hre
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => by positivity)
      (Eventually.of_forall fun k =>
        etaCriticalMirrorRightIndexNormalizedRotatedOriginalTail_le_audit hs k)

/-- On the left, the successor-index normalized mirror rotated tail vanishes. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖)
      atTop (nhds 0) := by
  have hupper :=
    etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTailPowerAudit_tendsto_zero hre
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => by positivity)
      (Eventually.of_forall fun k =>
        etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTail_le_audit hs k)

/-- Right normalized defect-minus-mirror complex remainder vanishes. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedDefectSubMirror_norm_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ‖etaCriticalMirrorPairFrameRotatedDefectTail s k -
            etaCriticalMirrorPairFrameRotatedMirrorTail s k‖)
      atTop (nhds 0) := by
  have hsubordinate :=
    etaCriticalMirrorRightIndexNormalizedRotatedOriginalTail_tendsto_zero
      hs hre
  refine hsubordinate.congr' ?_
  filter_upwards with k
  rw [etaCriticalMirrorPairFrameRotatedDefectTail_eq_mirror_sub_original hs k]
  congr 1
  ring_nf
  rw [norm_neg]

/-- Left normalized defect-plus-original complex remainder vanishes. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedDefectAddOriginal_norm_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ‖etaCriticalMirrorPairFrameRotatedDefectTail s k +
            etaCriticalMirrorPairFrameRotatedOriginalTail s k‖)
      atTop (nhds 0) := by
  have hsubordinate :=
    etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTail_tendsto_zero
      hs hre
  refine hsubordinate.congr' ?_
  filter_upwards with k
  rw [etaCriticalMirrorPairFrameRotatedDefectTail_eq_mirror_sub_original hs k]
  congr 1
  ring_nf

end DkMath.RH.CFBRCProjection
