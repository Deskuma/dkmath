/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFunctionalEquationOrbitAsymptoticAudit
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaFirstOrderOrbitAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- The functional-equation reflection of a nonzero point cannot equal `1`. -/
theorem one_sub_ne_one_of_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) :
    1 - s ≠ 1 := by
  intro h
  exact hs0 (sub_eq_self.mp h)

/--
Differentiating the completed-zeta functional equation gives the exact raw
first-order sign reversal.  The four non-pole assumptions merely ensure that
both derivatives are genuine derivatives of `completedRiemannZeta`.
-/
theorem completedRiemannZeta_deriv_one_sub_eq_neg
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (href0 : 1 - s ≠ 0) (href1 : 1 - s ≠ 1) :
    deriv completedRiemannZeta (1 - s) =
      -deriv completedRiemannZeta s := by
  have houter :
      HasDerivAt completedRiemannZeta
        (deriv completedRiemannZeta (1 - s)) (1 - s) :=
    (differentiableAt_completedZeta href0 href1).hasDerivAt
  have hinner :
      HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp :
      HasDerivAt
        (fun z : ℂ => completedRiemannZeta (1 - z))
        (deriv completedRiemannZeta (1 - s) * (-1)) s := by
    simpa [Function.comp_def] using houter.comp s hinner
  have hfun :
      (fun z : ℂ => completedRiemannZeta (1 - z)) =
        completedRiemannZeta := by
    funext z
    exact completedRiemannZeta_one_sub z
  rw [hfun] at hcomp
  have hdirect :
      HasDerivAt completedRiemannZeta
        (deriv completedRiemannZeta s) s :=
    (differentiableAt_completedZeta hs0 hs1).hasDerivAt
  have hu :
      deriv completedRiemannZeta (1 - s) * (-1) =
        deriv completedRiemannZeta s :=
    hcomp.unique hdirect
  calc
    deriv completedRiemannZeta (1 - s) =
        -(deriv completedRiemannZeta (1 - s) * (-1)) := by ring
    _ = -deriv completedRiemannZeta s := by rw [hu]

/-- The completed-zeta derivative sign law at a standard nontrivial zero. -/
theorem completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    deriv completedRiemannZeta (1 - s) =
      -deriv completedRiemannZeta s := by
  exact
    completedRiemannZeta_deriv_one_sub_eq_neg
      (nontrivialRiemannZetaZero_ne_zero hs)
      hs.2.2
      (one_sub_ne_zero_of_nontrivialRiemannZetaZero hs)
      (one_sub_ne_one_of_ne_zero
        (nontrivialRiemannZetaZero_ne_zero hs))

/--
The derivative at the reflected point, transported back through the tangent
map of `z ↦ 1 - z`.  The extra minus sign is the derivative of that reflection.
-/
noncomputable def completedZetaFunctionalReflectionTransportedDerivative
    (s : ℂ) : ℂ :=
  -deriv completedRiemannZeta (1 - s)

/--
After tangent transport, the functional-equation derivative is exactly the
original derivative.  Thus the raw minus sign is orientation data, not a
same-object contradiction.
-/
theorem completedZetaFunctionalReflectionTransportedDerivative_eq
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    completedZetaFunctionalReflectionTransportedDerivative s =
      deriv completedRiemannZeta s := by
  unfold completedZetaFunctionalReflectionTransportedDerivative
  rw [completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero hs]
  simp

/-- Functional reflection preserves the norm of the completed-zeta derivative. -/
theorem norm_completedRiemannZeta_deriv_one_sub_eq
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    ‖deriv completedRiemannZeta (1 - s)‖ =
      ‖deriv completedRiemannZeta s‖ := by
  rw [completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero hs,
    norm_neg]

/-- A value-and-first-derivative formulation of a simple completed-zeta zero. -/
def CompletedRiemannZetaSimpleZeroAt (s : ℂ) : Prop :=
  completedRiemannZeta s = 0 ∧
    deriv completedRiemannZeta s ≠ 0

/-- Simple-zero status is preserved by functional-equation reflection. -/
theorem completedRiemannZetaSimpleZeroAt_one_sub_iff
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    CompletedRiemannZetaSimpleZeroAt (1 - s) ↔
      CompletedRiemannZetaSimpleZeroAt s := by
  have hderiv :=
    completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero hs
  constructor
  · rintro ⟨hrefZero, hrefDeriv⟩
    refine ⟨?_, ?_⟩
    · simpa [completedRiemannZeta_one_sub] using hrefZero
    · intro hzero
      apply hrefDeriv
      rw [hderiv, hzero, neg_zero]
  · rintro ⟨hsZero, hsDeriv⟩
    refine ⟨?_, ?_⟩
    · simpa [completedRiemannZeta_one_sub] using hsZero
    · rw [hderiv]
      exact neg_ne_zero.mpr hsDeriv

/--
First-order functional-equation orbit certificate at a nontrivial zero.
It records both zero values, raw derivative antisymmetry, tangent-transported
derivative equality, and norm preservation.
-/
structure EtaCriticalMirrorCompletedZetaFirstOrderOrbitCompatibilityCertificate
    (s : ℂ) : Prop where
  original_zero : completedRiemannZeta s = 0
  reflected_zero : completedRiemannZeta (1 - s) = 0
  derivative_antisymmetry :
    deriv completedRiemannZeta (1 - s) =
      -deriv completedRiemannZeta s
  transported_derivative_eq :
    completedZetaFunctionalReflectionTransportedDerivative s =
      deriv completedRiemannZeta s
  derivative_norm_eq :
    ‖deriv completedRiemannZeta (1 - s)‖ =
      ‖deriv completedRiemannZeta s‖

/-- Build the complete first-order compatibility certificate. -/
theorem etaCriticalMirrorCompletedZetaFirstOrderOrbitCompatibilityCertificate_of_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    EtaCriticalMirrorCompletedZetaFirstOrderOrbitCompatibilityCertificate s :=
  { original_zero :=
      completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero hs
    reflected_zero :=
      completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs
    derivative_antisymmetry :=
      completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero hs
    transported_derivative_eq :=
      completedZetaFunctionalReflectionTransportedDerivative_eq hs
    derivative_norm_eq :=
      norm_completedRiemannZeta_deriv_one_sub_eq hs }

end DkMath.RH.CFBRCProjection
