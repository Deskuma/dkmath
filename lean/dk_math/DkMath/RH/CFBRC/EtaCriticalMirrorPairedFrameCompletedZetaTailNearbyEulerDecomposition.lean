/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyTransverseBridge
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameEtaTailEulerHalf
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerDecomposition"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- A point of positive real part cannot be a zero of Deligne's real Gamma factor. -/
theorem gammaR_ne_zero_of_pos_re
    {z : ℂ} (hz : 0 < z.re) :
    Complex.Gammaℝ z ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  have hre := congrArg Complex.re hn
  simp at hre
  linarith

/-- The canonical nearby point remains in the open right half-plane. -/
theorem completedZetaCanonicalNearbyPoint_re_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    0 < (s + completedZetaCanonicalDisplacement k).re := by
  have hsre := nontrivialRiemannZetaZero_re_pos hs
  unfold completedZetaCanonicalDisplacement
  simp only [Complex.add_re, Complex.ofReal_re]
  positivity

/-- On the open right half-plane, completed zeta is GammaR times ordinary zeta. -/
theorem completedRiemannZeta_eq_gammaR_mul_riemannZeta_of_pos_re
    {z : ℂ} (hz : 0 < z.re) :
    completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hz
  have hgamma := gammaR_ne_zero_of_pos_re hz
  have hzeta := riemannZeta_def_of_ne_zero hz0
  calc
    completedRiemannZeta z =
        Complex.Gammaℝ z *
          (completedRiemannZeta z / Complex.Gammaℝ z) := by
      field_simp [hgamma]
    _ = Complex.Gammaℝ z * riemannZeta z := by
      rw [← hzeta]

/-- The normalized nearby completed-zeta value has an exact GammaR-zeta factorization. -/
theorem normalizedNearbyCompletedZeta_eq_gammaR_mul_riemannZeta
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    (completedZetaCanonicalDisplacement k)⁻¹ *
        completedRiemannZeta
          (s + completedZetaCanonicalDisplacement k) =
      (completedZetaCanonicalDisplacement k)⁻¹ *
        (Complex.Gammaℝ
            (s + completedZetaCanonicalDisplacement k) *
          riemannZeta
            (s + completedZetaCanonicalDisplacement k)) := by
  rw [completedRiemannZeta_eq_gammaR_mul_riemannZeta_of_pos_re
    (completedZetaCanonicalNearbyPoint_re_pos hs k)]

/-- Euler half-endpoint main carrier of the dominant weighted complete defect tail. -/
noncomputable def etaCriticalMirrorDominantWeightedTailEulerMainCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantIndexPower k s *
    (((1 : ℂ) / 2) * etaUnsignedVector s (2 * (k + 1)) -
      ((1 : ℂ) / 2) *
        etaUnsignedVector (criticalMirror s) (2 * (k + 1)))

/-- Euler remainder carrier of the dominant weighted complete defect tail. -/
noncomputable def etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantIndexPower k s *
    (etaPairEulerRemainderTail (k + 1) s -
      etaPairEulerRemainderTail (k + 1) (criticalMirror s))

/-- Exact Euler main-plus-remainder decomposition of the dominant weighted tail. -/
theorem etaCriticalMirrorDominantWeightedTailCarrier_eq_eulerMain_add_remainder
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorDominantWeightedTailCarrier k s =
      etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s +
        etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s := by
  have hsre := nontrivialRiemannZetaZero_re_pos hs
  have hmre := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  unfold etaCriticalMirrorDominantWeightedTailCarrier
  rw [etaCriticalMirrorDefectPairTail_eq_etaPairTail_sub hsre hmre]
  rw [etaPairTail_eq_half_endpoint_add_eulerRemainderTail hsre]
  rw [etaPairTail_eq_half_endpoint_add_eulerRemainderTail hmre]
  unfold etaCriticalMirrorDominantWeightedTailEulerMainCarrier
  unfold etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier
  ring

/-- Euler-main mismatch against the GammaR-zeta form of the nearby completed value. -/
noncomputable def etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainMismatchCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s -
    (completedZetaCanonicalDisplacement k)⁻¹ *
      (Complex.Gammaℝ
          (s + completedZetaCanonicalDisplacement k) *
        riemannZeta
          (s + completedZetaCanonicalDisplacement k))

/-- Transverse error of the Euler-main / nearby-completed-zeta mismatch. -/
noncomputable def etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
    (completedZetaCanonicalSlopeDirection s)
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainMismatchCarrier k s)

/-- Transverse contribution of the weighted Euler remainder carrier. -/
noncomputable def etaCriticalMirrorWeightedTailEulerRemainderTransverseError
    (k : ℕ) (s : ℂ) : ℝ :=
  complexRealLineDefect
    (completedZetaCanonicalSlopeDirection s)
    (etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s)

/-- The full tail/nearby transverse bridge splits exactly into main mismatch and remainder. -/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError k s =
      etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError k s +
        etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s := by
  unfold etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError
  rw [etaCriticalMirrorDominantWeightedTailCarrier_eq_eulerMain_add_remainder hs]
  rw [normalizedNearbyCompletedZeta_eq_gammaR_mul_riemannZeta hs]
  unfold etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError
  unfold etaCriticalMirrorWeightedTailEulerRemainderTransverseError
  unfold etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainMismatchCarrier
  simp [complexRealLineDefect, mul_add]; ring

/-- Main transverse mismatch collapse. -/
def EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError
          k s)
      atTop (nhds 0)

/-- Euler remainder transverse collapse. -/
def EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s)
      atTop (nhds 0)

/-- Main mismatch collapse plus Euler remainder collapse supplies the full bridge. -/
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_of_eulerMain_and_remainder
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse)
    (hrem : EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse) :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse := by
  intro s hs him
  have hsum := (hmain hs him).add (hrem hs him)
  have hsum' :
      Tendsto
        (fun k : ℕ =>
          etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError k s +
            etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s)
        atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  refine hsum'.congr' (Eventually.of_forall fun k => ?_)
  exact
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
      hs k).symm

/-- RH follows from the Euler-main bridge together with remainder collapse. -/
theorem riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMain_and_remainder
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse)
    (hrem : EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse) :
    RiemannHypothesis :=
  riemannHypothesis_of_weightedTailCompletedZetaNearbyTransverseBridgeCollapse
    (etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_of_eulerMain_and_remainder
      hmain hrem)

#print axioms completedRiemannZeta_eq_gammaR_mul_riemannZeta_of_pos_re
#print axioms etaCriticalMirrorDominantWeightedTailCarrier_eq_eulerMain_add_remainder
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMain_and_remainder

end DkMath.RH.CFBRCProjection
