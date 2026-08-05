/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionClosure
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeGlobalLine"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Canonical nonzero real displacement used to probe completed zeta at a zero. -/
noncomputable def completedZetaCanonicalDisplacement
    (k : ℕ) : ℂ :=
  (((1 : ℝ) / (((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ)

/--
Canonical completed-zeta slope carrier based at `s`.

At a completed-zeta zero this is the normalized value of completed zeta at the
nearby point `s + 1 / (k + 1)`.  The carrier is defined independently of the
eta endpoint and independently of the critical-line conclusion.
-/
noncomputable def completedZetaCanonicalSlopeCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  (completedZetaCanonicalDisplacement k)⁻¹ *
    (completedRiemannZeta (s + completedZetaCanonicalDisplacement k) -
      completedRiemannZeta s)

/--
Canonical fixed direction of the completed-zeta slope carrier.

When the first derivative is nonzero, the derivative itself is used.  At a
multiple zero whose first derivative vanishes, direction `1` is used; the
slope carrier then converges to zero and therefore approaches every fixed real
line.  This avoids any simplicity assumption on nontrivial zeros.
-/
noncomputable def completedZetaCanonicalSlopeDirection
    (s : ℂ) : ℂ :=
  if deriv completedRiemannZeta s = 0 then 1
  else deriv completedRiemannZeta s

/-- The canonical displacement converges to zero. -/
theorem completedZetaCanonicalDisplacement_tendsto_zero :
    Tendsto completedZetaCanonicalDisplacement atTop (nhds 0) := by
  have hreal :
      Tendsto
        (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have h :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (show Tendsto (fun k : ℕ => k + 1) atTop atTop from by
          refine tendsto_atTop.2 ?_
          intro b
          exact eventually_atTop.2 ⟨b, by omega⟩)
    simpa [Function.comp_def] using h
  have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
  simpa [completedZetaCanonicalDisplacement, Function.comp_def] using hcast

/-- Every canonical displacement is nonzero. -/
theorem completedZetaCanonicalDisplacement_ne_zero
    (k : ℕ) :
    completedZetaCanonicalDisplacement k ≠ 0 := by
  unfold completedZetaCanonicalDisplacement
  have hden : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  exact_mod_cast (div_ne_zero one_ne_zero hden)

/-- The canonical displacement converges through the punctured neighborhood. -/
theorem completedZetaCanonicalDisplacement_tendsto_punctured :
    Tendsto completedZetaCanonicalDisplacement atTop
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨completedZetaCanonicalDisplacement_tendsto_zero, ?_⟩
  exact Eventually.of_forall fun k => by
    simpa using completedZetaCanonicalDisplacement_ne_zero k

/-- The canonical completed-zeta slope carrier converges to the derivative. -/
theorem completedZetaCanonicalSlopeCarrier_tendsto_deriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Tendsto
      (fun k : ℕ => completedZetaCanonicalSlopeCarrier k s)
      atTop (nhds (deriv completedRiemannZeta s)) := by
  have hslope :=
    (differentiableAt_completedZeta hs0 hs1).hasDerivAt.tendsto_slope_zero
  have hcomp :=
    hslope.comp completedZetaCanonicalDisplacement_tendsto_punctured
  simpa [completedZetaCanonicalSlopeCarrier, smul_eq_mul] using hcomp

/-- The canonical completed-zeta direction never vanishes. -/
theorem completedZetaCanonicalSlopeDirection_ne_zero
    (s : ℂ) :
    completedZetaCanonicalSlopeDirection s ≠ 0 := by
  by_cases hderiv : deriv completedRiemannZeta s = 0
  · simp [completedZetaCanonicalSlopeDirection, hderiv]
  · simpa [completedZetaCanonicalSlopeDirection, hderiv] using hderiv

/-- The derivative lies on the real line selected by the canonical direction. -/
theorem completedZetaCanonicalSlopeDirection_inv_mul_deriv_im_eq_zero
    (s : ℂ) :
    ((completedZetaCanonicalSlopeDirection s)⁻¹ *
      deriv completedRiemannZeta s).im = 0 := by
  by_cases hderiv : deriv completedRiemannZeta s = 0
  · simp [completedZetaCanonicalSlopeDirection, hderiv]
  · rw [completedZetaCanonicalSlopeDirection, if_neg hderiv,
      inv_mul_cancel₀ hderiv]
    norm_num

/--
The completed-zeta slope carrier approaches one fixed real line at every
standard nontrivial zero.  This is a genuine global-line construction: its
direction comes only from completed zeta and is independent of the eta pair
index.
-/
theorem completedZetaCanonicalSlopeCarrier_tendsto_global_line
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (completedZetaCanonicalSlopeCarrier k s))
      atTop (nhds 0) := by
  have hcarrier :=
    completedZetaCanonicalSlopeCarrier_tendsto_deriv
      (nontrivialRiemannZetaZero_ne_zero hs) hs.2.2
  have hrotated :
      Tendsto
        (fun k : ℕ =>
          (completedZetaCanonicalSlopeDirection s)⁻¹ *
            completedZetaCanonicalSlopeCarrier k s)
        atTop
        (nhds
          ((completedZetaCanonicalSlopeDirection s)⁻¹ *
            deriv completedRiemannZeta s)) := by
    exact
      (show Tendsto
          (fun _ : ℕ => (completedZetaCanonicalSlopeDirection s)⁻¹)
          atTop
          (nhds (completedZetaCanonicalSlopeDirection s)⁻¹) from
        tendsto_const_nhds).mul hcarrier
  have himaginary :=
    (Complex.continuous_im.tendsto
      ((completedZetaCanonicalSlopeDirection s)⁻¹ *
        deriv completedRiemannZeta s)).comp hrotated
  simpa [complexRealLineDefect, Function.comp_def,
    completedZetaCanonicalSlopeDirection_inv_mul_deriv_im_eq_zero] using
      himaginary

/-- The canonical completed-zeta slope carrier has an unconditional global lock. -/
noncomputable def completedZetaCanonicalSlopeGlobalZeroLineLock :
    EtaCriticalMirrorGlobalZeroLineLock
      completedZetaCanonicalSlopeCarrier where
  globalDirection := completedZetaCanonicalSlopeDirection
  globalDirection_ne_zero := by
    intro s _hs _him
    exact completedZetaCanonicalSlopeDirection_ne_zero s
  carrier_tendsto_global_line := by
    intro s hs _him
    exact completedZetaCanonicalSlopeCarrier_tendsto_global_line hs

/--
Two carriers are asymptotically the same on the standard nontrivial zero locus
when their difference tends to zero at every nonreal zero.
-/
def EtaCriticalMirrorZeroLocusCarrierAsymptoticEquivalent
    (carrier target : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ => carrier k s - target k s)
      atTop (nhds 0)

/-- A global zero-line lock transfers across zero-locus asymptotic equivalence. -/
theorem EtaCriticalMirrorGlobalZeroLineLock.of_asymptoticEquivalent
    {carrier target : ℕ → ℂ → ℂ}
    (hglobal : EtaCriticalMirrorGlobalZeroLineLock target)
    (heq :
      EtaCriticalMirrorZeroLocusCarrierAsymptoticEquivalent carrier target) :
    EtaCriticalMirrorGlobalZeroLineLock carrier where
  globalDirection := hglobal.globalDirection
  globalDirection_ne_zero := hglobal.globalDirection_ne_zero
  carrier_tendsto_global_line := by
    intro s hs him
    let direction : ℂ := hglobal.globalDirection s
    have htarget := hglobal.carrier_tendsto_global_line hs him
    have hdiff := heq hs him
    have hrotatedDiff :
        Tendsto
          (fun k : ℕ =>
            direction⁻¹ * (carrier k s - target k s))
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        (show Tendsto (fun _ : ℕ => direction⁻¹) atTop (nhds direction⁻¹) from
          tendsto_const_nhds).mul hdiff
    have himaginaryDiff :
        Tendsto
          (fun k : ℕ =>
            (direction⁻¹ * (carrier k s - target k s)).im)
          atTop (nhds 0) := by
      have h := (Complex.continuous_im.tendsto 0).comp hrotatedDiff
      simpa [Function.comp_def] using h
    have hsum := htarget.add himaginaryDiff
    refine hsum.congr' (Eventually.of_forall fun k => ?_)
    unfold complexRealLineDefect
    dsimp [direction]
    have hidentity :
        (hglobal.globalDirection s)⁻¹ * carrier k s =
          (hglobal.globalDirection s)⁻¹ * target k s +
            (hglobal.globalDirection s)⁻¹ *
              (carrier k s - target k s) := by
      ring
    rw [hidentity, Complex.add_im]

/--
The final same-object analytic bridge.

It asks that the already constructed dominant eta endpoint carrier and the
canonical completed-zeta slope carrier represent the same normalized zero
locus object asymptotically.  No line direction and no critical-line conclusion
is included in this predicate.
-/
def EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility : Prop :=
  EtaCriticalMirrorZeroLocusCarrierAsymptoticEquivalent
    etaCriticalMirrorDominantNormalizedEndpointCarrier
    completedZetaCanonicalSlopeCarrier

/-- Endpoint/slope compatibility supplies the genuine endpoint global-line lock. -/
theorem etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    EtaCriticalMirrorGlobalZeroLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier :=
  completedZetaCanonicalSlopeGlobalZeroLineLock.of_asymptoticEquivalent hcompat

/--
The Riemann Hypothesis follows from the single explicit endpoint/slope
compatibility bridge.  The global line itself is already constructed from the
completed-zeta derivative and contains no RH-equivalent premise.
-/
theorem riemannHypothesis_of_endpointCompletedZetaSlopeCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointGlobalZeroLineLock
    (etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
      hcompat)

#print axioms completedZetaCanonicalSlopeGlobalZeroLineLock
#print axioms etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeCompatibility

end DkMath.RH.CFBRCProjection
