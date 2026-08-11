/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeGlobalLine
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaSlopeCompatibilityAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
Full endpoint/slope value compatibility forces the dominant endpoint carrier
itself to converge to the completed-zeta derivative.

This exposes the strength hidden in the raw difference-to-zero formulation:
it is not merely a line-direction statement.
-/
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_tendsto_deriv_of_completedZetaSlopeCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantNormalizedEndpointCarrier k s)
      atTop (nhds (deriv completedRiemannZeta s)) := by
  have hdiff := hcompat hs him
  have hslope :=
    completedZetaCanonicalSlopeCarrier_tendsto_deriv
      (nontrivialRiemannZetaZero_ne_zero hs) hs.2.2
  have hsum := hdiff.add hslope
  have hsum' :
      Tendsto
        (fun k : ℕ =>
          (etaCriticalMirrorDominantNormalizedEndpointCarrier k s -
              completedZetaCanonicalSlopeCarrier k s) +
            completedZetaCanonicalSlopeCarrier k s)
        atTop (nhds (deriv completedRiemannZeta s)) := by
    simpa only [zero_add] using hsum
  refine hsum'.congr' (Eventually.of_forall fun k => ?_)
  ring

/--
At an off-critical zero, full endpoint/slope value compatibility identifies
the norm of the completed-zeta derivative with the explicit dominant eta-tail
constant on the corresponding side.
-/
theorem norm_deriv_completedRiemannZeta_eq_dominantTailConstant_of_completedZetaSlopeCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    (s.re < (1 : ℝ) / 2 ∧
        ‖deriv completedRiemannZeta s‖ =
          ‖-etaPairIndexNormalizedTailConstant s‖) ∨
      ((1 : ℝ) / 2 < s.re ∧
        ‖deriv completedRiemannZeta s‖ =
          ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖) := by
  have hendpoint :=
    etaCriticalMirrorDominantNormalizedEndpointCarrier_tendsto_deriv_of_completedZetaSlopeCompatibility
      hcompat hs him
  have hnormEndpoint :
      Tendsto
        (fun k : ℕ =>
          ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖)
        atTop (nhds ‖deriv completedRiemannZeta s‖) := by
    change Tendsto
      ((fun z : ℂ => ‖z‖) ∘
        fun k : ℕ =>
          etaCriticalMirrorDominantNormalizedEndpointCarrier k s)
      atTop (nhds ‖deriv completedRiemannZeta s‖)
    simpa only [Function.comp_apply] using
      (continuous_norm.tendsto (deriv completedRiemannZeta s)).comp hendpoint
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have hle : s.re ≤ (1 : ℝ) / 2 := le_of_lt hleft
    have hcert :=
      (etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hleft).endpoint_norm_tendsto
    have hcert' :
        Tendsto
          (fun k : ℕ =>
            ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖)
          atTop (nhds ‖-etaPairIndexNormalizedTailConstant s‖) := by
      simpa only [etaCriticalMirrorDominantNormalizedEndpointCarrier,
        if_pos hle] using hcert
    exact Or.inl
      ⟨hleft, tendsto_nhds_unique hnormEndpoint hcert'⟩
  · have hnotle : ¬ s.re ≤ (1 : ℝ) / 2 := not_le.mpr hright
    have hcert :=
      (etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
        hs him hright).endpoint_norm_tendsto
    have hcert' :
        Tendsto
          (fun k : ℕ =>
            ‖etaCriticalMirrorDominantNormalizedEndpointCarrier k s‖)
          atTop
          (nhds ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖) := by
      simpa only [etaCriticalMirrorDominantNormalizedEndpointCarrier,
        if_neg hnotle] using hcert
    exact Or.inr
      ⟨hright, tendsto_nhds_unique hnormEndpoint hcert'⟩

/--
Full endpoint/slope value compatibility forces every hypothetical off-critical
nontrivial zero to be a simple completed-zeta zero.

This is an audit result, not an added premise: it shows that direct carrier
value equivalence contains strictly more information than the line lock needed
by the moving-line collision theorem.
-/
theorem deriv_completedRiemannZeta_ne_zero_of_completedZetaSlopeCompatibility_of_offCritical
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    deriv completedRiemannZeta s ≠ 0 := by
  have hnorm :=
    norm_deriv_completedRiemannZeta_eq_dominantTailConstant_of_completedZetaSlopeCompatibility
      hcompat hs him hre
  intro hderiv
  rcases hnorm with hleft | hright
  · have hconstant : ‖-etaPairIndexNormalizedTailConstant s‖ ≠ 0 :=
      norm_ne_zero_iff.mpr
        (neg_ne_zero.mpr (etaPairIndexNormalizedTailConstant_ne_zero s))
    apply hconstant
    rw [← hleft.2, hderiv, norm_zero]
  · have hconstant :
        ‖etaPairIndexNormalizedTailConstant (criticalMirror s)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr
        (etaPairIndexNormalizedTailConstant_ne_zero (criticalMirror s))
    apply hconstant
    rw [← hright.2, hderiv, norm_zero]

/--
The minimal completed-zeta slope condition actually consumed by the final
collision route: the dominant endpoint approaches the fixed real line selected
by the completed-zeta derivative direction.

Unlike full carrier value compatibility, this predicate does not assert that
the endpoint converges to the derivative or has the same norm.
-/
def EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorDominantNormalizedEndpointCarrier k s))
      atTop (nhds 0)

/-- Full value compatibility implies the weaker line-only compatibility. -/
theorem etaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility_of_valueCompatibility
    (hcompat : EtaCriticalMirrorEndpointCompletedZetaSlopeCompatibility) :
    EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility := by
  intro s hs him
  exact
    (etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeCompatibility
      hcompat).carrier_tendsto_global_line hs him

/-- The line-only compatibility builds the exact endpoint global lock needed by RH closure. -/
noncomputable def etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeLineCompatibility
    (hline : EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility) :
    EtaCriticalMirrorGlobalZeroLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier where
  globalDirection := completedZetaCanonicalSlopeDirection
  globalDirection_ne_zero := by
    intro s _hs _him
    exact completedZetaCanonicalSlopeDirection_ne_zero s
  carrier_tendsto_global_line := by
    intro s hs him
    exact hline hs him

/--
The Riemann Hypothesis follows from the minimal line-only completed-zeta slope
compatibility.  No endpoint/derivative value equality is required.
-/
theorem riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility
    (hline : EtaCriticalMirrorEndpointCompletedZetaSlopeLineCompatibility) :
    RiemannHypothesis :=
  riemannHypothesis_of_endpointGlobalZeroLineLock
    (etaCriticalMirrorEndpointGlobalZeroLineLock_of_completedZetaSlopeLineCompatibility
      hline)

#print axioms etaCriticalMirrorDominantNormalizedEndpointCarrier_tendsto_deriv_of_completedZetaSlopeCompatibility
#print axioms deriv_completedRiemannZeta_ne_zero_of_completedZetaSlopeCompatibility_of_offCritical
#print axioms riemannHypothesis_of_endpointCompletedZetaSlopeLineCompatibility

end DkMath.RH.CFBRCProjection
