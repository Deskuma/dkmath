/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerDecomposition
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerRemainderCollapse"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- One Euler remainder tail scaled by an arbitrary real index exponent. -/
noncomputable def etaPairIndexScaledEulerRemainder
    (a : ℝ) (z : ℂ) (k : ℕ) : ℂ :=
  (((((k + 1 : ℕ) : ℝ)) ^ a : ℝ) : ℂ) *
    etaPairEulerRemainderTail (k + 1) z

/--
A weaker index exponent is norm-dominated by the already constructed
full `re z`-normalized rotated Euler remainder.
-/
theorem norm_etaPairIndexScaledEulerRemainder_le_normalized
    {a : ℝ} {z : ℂ} (ha : a ≤ z.re) (k : ℕ) :
    ‖etaPairIndexScaledEulerRemainder a z k‖ ≤
      ‖etaPairIndexNormalizedRotatedEulerRemainder z k‖ := by
  have hbase : 1 ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hscale :
      (((k + 1 : ℕ) : ℝ) ^ a) ≤
        (((k + 1 : ℕ) : ℝ) ^ z.re) :=
    Real.rpow_le_rpow_of_exponent_le hbase ha
  have hscaleA : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ a) :=
    Real.rpow_nonneg _ _
  have hscaleZ : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ z.re) :=
    Real.rpow_nonneg _ _
  unfold etaPairIndexScaledEulerRemainder
  unfold etaPairIndexNormalizedRotatedEulerRemainder
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscaleA, abs_of_nonneg hscaleZ,
    norm_etaPairBaseRotation, one_mul]
  exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)

/-- Every weaker-than-natural normalized Euler remainder still tends to zero. -/
theorem etaPairIndexScaledEulerRemainder_tendsto_zero
    {a : ℝ} {z : ℂ} (hzre : 0 < z.re) (ha : a ≤ z.re) :
    Tendsto
      (etaPairIndexScaledEulerRemainder a z)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper :
      Tendsto
        (fun k : ℕ =>
          ‖etaPairIndexNormalizedRotatedEulerRemainder z k‖)
        atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp
      (etaPairIndexNormalizedRotatedEulerRemainder_tendsto_zero hzre)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => norm_nonneg _)
      (Eventually.of_forall fun k =>
        norm_etaPairIndexScaledEulerRemainder_le_normalized ha k)

/--
The side-aware dominant weighted Euler remainder carrier tends to zero on every
standard nontrivial zero.  No critical-line conclusion is used.
-/
theorem etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s)
      atTop (nhds 0) := by
  have hsre : 0 < s.re := nontrivialRiemannZetaZero_re_pos hs
  have hmre : 0 < (criticalMirror s).re :=
    criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  by_cases hside : s.re ≤ (2 : ℝ)⁻¹
  · have hmirror : s.re ≤ (criticalMirror s).re := by
      simp only [criticalMirror_re]
      have hhalf : s.re ≤ (1 : ℝ) / 2 := by simpa using hside
      linarith
    have hsTail :
        Tendsto
          (etaPairIndexScaledEulerRemainder s.re s)
          atTop (nhds 0) :=
      etaPairIndexScaledEulerRemainder_tendsto_zero hsre le_rfl
    have hmTail :
        Tendsto
          (etaPairIndexScaledEulerRemainder s.re (criticalMirror s))
          atTop (nhds 0) :=
      etaPairIndexScaledEulerRemainder_tendsto_zero hmre hmirror
    have hdiff := hsTail.sub hmTail
    refine hdiff.congr' (Eventually.of_forall fun k => ?_)
    unfold etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier
    unfold etaCriticalMirrorDominantIndexPower
    unfold etaPairIndexScaledEulerRemainder
    simp only [if_pos hside]
    ring
  · have horiginal : (criticalMirror s).re ≤ s.re := by
      simp only [criticalMirror_re]
      have hhalf : (1 : ℝ) / 2 < s.re := by
        have : ¬ s.re ≤ (1 : ℝ) / 2 := by simpa using hside
        exact lt_of_not_ge this
      linarith
    have hsTail :
        Tendsto
          (etaPairIndexScaledEulerRemainder (criticalMirror s).re s)
          atTop (nhds 0) :=
      etaPairIndexScaledEulerRemainder_tendsto_zero hsre horiginal
    have hmTail :
        Tendsto
          (etaPairIndexScaledEulerRemainder
            (criticalMirror s).re (criticalMirror s))
          atTop (nhds 0) :=
      etaPairIndexScaledEulerRemainder_tendsto_zero hmre le_rfl
    have hdiff := hsTail.sub hmTail
    refine hdiff.congr' (Eventually.of_forall fun k => ?_)
    unfold etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier
    unfold etaCriticalMirrorDominantIndexPower
    unfold etaPairIndexScaledEulerRemainder
    simp only [if_neg hside]
    ring

/-- The weighted Euler remainder contributes no asymptotic transverse defect. -/
theorem etaCriticalMirrorWeightedTailEulerRemainderTransverseError_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s)
      atTop (nhds 0) := by
  have hcarrier :=
    etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier_tendsto_zero hs
  have hrotated :
      Tendsto
        (fun k : ℕ =>
          (completedZetaCanonicalSlopeDirection s)⁻¹ *
            etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s)
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (show Tendsto
          (fun _ : ℕ => (completedZetaCanonicalSlopeDirection s)⁻¹)
          atTop (nhds (completedZetaCanonicalSlopeDirection s)⁻¹) from
        tendsto_const_nhds).mul hcarrier
  have himaginary := (Complex.continuous_im.tendsto 0).comp hrotated
  simpa [etaCriticalMirrorWeightedTailEulerRemainderTransverseError,
    complexRealLineDefect, Function.comp_def] using himaginary

/-- The Euler remainder transverse-collapse contract is unconditional. -/
theorem etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse :
    EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse := by
  intro s hs _him
  exact etaCriticalMirrorWeightedTailEulerRemainderTransverseError_tendsto_zero hs

/-- With the remainder closed, the full bridge is equivalent to its Euler main part. -/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_eulerMain :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse ↔
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse := by
  constructor
  · intro hfull s hs him
    have hbridge := hfull hs him
    have hrem :=
      etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse hs him
    have hdiff := hbridge.sub hrem
    have hdiff' :
        Tendsto
          (fun k : ℕ =>
            etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError k s -
              etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s)
          atTop (nhds 0) := by
      simpa only [sub_zero] using hdiff
    refine hdiff'.congr' (Eventually.of_forall fun k => ?_)
    rw [
      etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
        hs]
    ring
  · intro hmain
    exact
      etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_of_eulerMain_and_remainder
        hmain etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse

/-- RH now follows from the Euler-main / nearby-completed-zeta mismatch alone. -/
theorem riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMainTransverseCollapse
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_eulerMain.mpr
      hmain)

#print axioms etaPairIndexScaledEulerRemainder_tendsto_zero
#print axioms etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier_tendsto_zero
#print axioms etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_eulerMain
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMainTransverseCollapse

end DkMath.RH.CFBRCProjection
