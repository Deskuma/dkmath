/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.Basic

#print "file: DkMath.CosmicFormula.ThreeElement.MagicCore"

/-!
# Static magic-core realizations for three-element states

This module proves that every nonnegative real target `B` has algebraic
witnesses in each of the three element forms:

* `coreTerm x = B`;
* `interactionBeam x x = B` with a symmetric interaction root;
* `gapTerm u = B`.

The structure in this file supplies algebraic witnesses only. It does not
assert that an existing flow converges to these witnesses. In particular, it
contains no `Filter.Tendsto` field and must not be used as a dynamic
assimilation provider.
-/

namespace DkMath
namespace CosmicFormula
namespace ThreeElement

/--
A canonical static realization of a target `B` by the three element forms.

The interaction Beam is deliberately realized by one symmetric root used on
both sides. This records static representability only, not a state transition
or a convergence theorem.
-/
structure SymmetricMagicCoreRealization (B : ℝ) where
  coreRoot : ℝ
  interactionRoot : ℝ
  gapRoot : ℝ
  core_realizes :
    coreTerm coreRoot = B
  interaction_realizes :
    interactionBeam interactionRoot interactionRoot = B
  gap_realizes :
    gapTerm gapRoot = B

/-- The square root of a nonnegative target realizes its Core form. -/
theorem core_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    coreTerm (Real.sqrt B) = B := by
  simpa only [coreTerm] using Real.sq_sqrt hB

/-- The square root of a nonnegative target realizes its Gap form. -/
theorem gap_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    gapTerm (Real.sqrt B) = B := by
  simpa only [gapTerm] using Real.sq_sqrt hB

/--
The symmetric root `sqrt (B / 2)` realizes a nonnegative target through the
interaction Beam `2*x*u`.
-/
theorem symmetric_interaction_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    interactionBeam
      (Real.sqrt (B / 2))
      (Real.sqrt (B / 2)) = B := by
  have hB2 : 0 ≤ B / 2 := by
    positivity
  calc
    interactionBeam
        (Real.sqrt (B / 2))
        (Real.sqrt (B / 2)) =
        2 * (Real.sqrt (B / 2)) ^ 2 := by
          simp only [interactionBeam]
          ring
    _ = 2 * (B / 2) := by
      rw [Real.sq_sqrt hB2]
    _ = B := by
      ring

/--
The canonical symmetric static realization of a nonnegative target `B`.

This definition packages only algebraic witnesses. It does not infer dynamic
assimilation from the square-root construction.
-/
def symmetricMagicCoreRealization
    (B : ℝ) (hB : 0 ≤ B) :
    SymmetricMagicCoreRealization B where
  coreRoot := Real.sqrt B
  interactionRoot := Real.sqrt (B / 2)
  gapRoot := Real.sqrt B
  core_realizes := core_sqrt_realizes hB
  interaction_realizes := symmetric_interaction_sqrt_realizes hB
  gap_realizes := gap_sqrt_realizes hB

end ThreeElement
end CosmicFormula
end DkMath
