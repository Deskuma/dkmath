/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFixedTorsion

#print "file: DkMath.Lib.NumberTheory.EllipticBaseChangeTorsion"

/-!
# Base-change transport for torsion points

The Frey construction first produces a point on a rational Weierstrass model,
while local and Galois arguments often use the same point after extending the
coefficient field to an algebraic closure.  This file isolates the elementary
transport that is actually needed at that boundary:

* `baseChangePoint` is additive, so it commutes with every natural multiple;
* injectivity of the coefficient embedding preserves the additive order.

No local valuation, Néron model, or torsion classification is involved.  The
lemmas are therefore safe to reuse before choosing a particular local place.
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

open WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] (E : WeierstrassCurve K)

/-- [DkMath.Lib] Base change of a rational point commutes with `nsmul`. -/
theorem baseChangePoint_nsmul (n : ℕ) (P : E.toAffine.Point) :
    baseChangePoint E (n • P) = n • baseChangePoint E P := by
  classical
  exact (baseChangePointHom E).map_nsmul n P

/-- [DkMath.Lib] The additive order of a point is preserved by base change. -/
theorem addOrderOf_baseChangePoint_eq (P : E.toAffine.Point) :
    addOrderOf (baseChangePoint E P) = addOrderOf P := by
  classical
  exact (addOrderOf_injective (baseChangePointHom E)
    (baseChangePoint_injective E) P)

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
