/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyRationalTwoPTorsion

#print "file: DkMathTest.FLT.FreyRationalTwoPTorsion"

namespace DkMathTest.FreyRationalTwoPTorsion

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 教科書回帰例：Cofixed 枝から商整数モデル上の厳密な `2*p` 捩れを得る。 -/
example (hp2 : p ≠ 2) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hL.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p :=
  residual_cofixed_implies_rational_two_p_torsion S hp2 hbe L hline hL

/-- 教科書回帰例：`a ≡ 7 mod 8` から偶数性を自動供給する。 -/
example (hp2 : p ≠ 2) (ha8 : S.a % 8 = 7)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hL.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p :=
  residual_cofixed_implies_rational_two_p_torsion_of_seven S hp2 ha8 L hline hL

#print axioms DkMath.FLT.Frey.Source.residual_cofixed_implies_rational_two_p_torsion
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_implies_rational_two_p_torsion_of_seven

end DkMathTest.FreyRationalTwoPTorsion
