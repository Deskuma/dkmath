/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay
import DkMath.RH.Weave.Analytic.EtaPairIntegral
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open DkMath.RH.Weave.Analytic

/--
Continuous mirror-minus-original derivative kernel underlying one paired
critical-mirror defect.
-/
def etaCriticalMirrorDefectPairIntegralKernel
    (s : ℂ) (x : ℝ) : ℂ :=
  etaPairIntegralKernel (criticalMirror s) x -
    etaPairIntegralKernel s x

/-- The continuous paired-defect kernel is integrable on each positive interval. -/
theorem etaCriticalMirrorDefectPairIntegralKernel_intervalIntegrable
    (s : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (etaCriticalMirrorDefectPairIntegralKernel s) volume a b := by
  change
    IntervalIntegrable
      (fun x : ℝ =>
        etaPairIntegralKernel (criticalMirror s) x -
          etaPairIntegralKernel s x) volume a b
  exact
    (etaPairIntegralKernel_intervalIntegrable
      (criticalMirror s) ha hab).sub
      (etaPairIntegralKernel_intervalIntegrable s ha hab)

/--
Exact integral identity for one paired critical-mirror defect.

The discrete defect pair is the interval integral of the mirror derivative
kernel minus the original derivative kernel.  Thus no phase information is
lost by passing from the adjacent eta pair to the continuous representation.
-/
theorem etaCriticalMirrorDefectPairTerm_eq_intervalIntegral
    {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaCriticalMirrorDefectPairIntegralKernel s x := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hmInt :
      IntervalIntegrable
        (etaPairIntegralKernel (criticalMirror s)) volume a b :=
    etaPairIntegralKernel_intervalIntegrable
      (criticalMirror s) ha hab
  have hsInt :
      IntervalIntegrable (etaPairIntegralKernel s) volume a b :=
    etaPairIntegralKernel_intervalIntegrable s ha hab
  rw [etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub,
    etaPairTerm_eq_intervalIntegral hm,
    etaPairTerm_eq_intervalIntegral hs]
  change
    (∫ x : ℝ in a..b,
      etaPairIntegralKernel (criticalMirror s) x) -
        (∫ x : ℝ in a..b, etaPairIntegralKernel s x) =
      ∫ x : ℝ in a..b,
        etaCriticalMirrorDefectPairIntegralKernel s x
  rw [← intervalIntegral.integral_sub hmInt hsInt]
  rfl

/-- A nontrivial zeta zero is nonzero as a complex number. -/
theorem nontrivialRiemannZetaZero_ne_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s ≠ 0 := by
  intro hs0
  have hre := nontrivialRiemannZetaZero_re_pos hs
  simp [hs0] at hre

/-- The critical mirror of a nontrivial zeta zero is nonzero. -/
theorem criticalMirror_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    criticalMirror s ≠ 0 := by
  intro hm0
  have hre := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
  simp [hm0] at hre

/-- Every nontrivial zeta zero has the exact paired-defect integral representation. -/
theorem etaCriticalMirrorDefectPairTerm_eq_intervalIntegral_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorDefectPairTerm s k =
      ∫ x : ℝ in (((2 * k + 1 : ℕ) : ℝ))..
          (((2 * k + 2 : ℕ) : ℝ)),
        etaCriticalMirrorDefectPairIntegralKernel s x :=
  etaCriticalMirrorDefectPairTerm_eq_intervalIntegral
    (nontrivialRiemannZetaZero_ne_zero hs)
    (criticalMirror_ne_zero_of_nontrivialRiemannZetaZero hs)
    k

end DkMath.RH.CFBRCProjection
