/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothTorsionOrderBound

#print "file: DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionOrderBound"

namespace DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionOrderBound

open DkMath.Lib.NumberTheory

noncomputable section

variable {L : Type*} [Field L] [CharZero L]

noncomputable local instance instDecidableEqEllipticSmoothTorsionOrderBoundTest
    {α : Type*} : DecidableEq α := Classical.decEq _

/-- 教科書回帰例：良還元上の `n`-捩れ点の位数は剰余体点数で抑えられる。 -/
example (A : ValuationSubring L) (W : WeierstrassCurve A)
    [Fintype (IsLocalRing.ResidueField A)]
    (hgood : (W.map (IsLocalRing.residue A)).Δ ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) {n : ℕ}
    (hn : A.valuation (n : L) = 1) (hQ : n • Q = 0) :
    addOrderOf Q ≤ 2 * Fintype.card (IsLocalRing.ResidueField A) + 1 :=
  addOrderOf_le_two_mul_residue_card_add_one_of_good A W hgood Q hn hQ

#print axioms addOrderOf_le_two_mul_residue_card_add_one_of_good

end
end DkMathTest.Lib.NumberTheory.EllipticSmoothTorsionOrderBound
