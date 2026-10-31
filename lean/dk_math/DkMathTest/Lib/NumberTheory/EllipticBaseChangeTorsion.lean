/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticBaseChangeTorsion

#print "file: DkMathTest.Lib.NumberTheory.EllipticBaseChangeTorsion"

namespace DkMathTest.Lib.NumberTheory.EllipticBaseChangeTorsion

open WeierstrassCurve
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] (E : WeierstrassCurve K)

example (n : ℕ) (P : E.toAffine.Point) :
    baseChangePoint E (n • P) = n • baseChangePoint E P :=
  baseChangePoint_nsmul E n P

example (P : E.toAffine.Point) :
    addOrderOf (baseChangePoint E P) = addOrderOf P :=
  addOrderOf_baseChangePoint_eq E P

#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.baseChangePoint_nsmul
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.addOrderOf_baseChangePoint_eq

end
end DkMathTest.Lib.NumberTheory.EllipticBaseChangeTorsion
