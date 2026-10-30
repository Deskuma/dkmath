/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoSmallGoodPrime

#print "file: DkMath.FLT.FreyHnoThreeGood"

/-!
# NOTE-032: `q = 3` の良還元から得る条件付き hno

この章は、Cofixed な一次元核から作られる有理 `2 * p` 捩れ点を、整数商モデルの
`3` 上の良還元へ輸送する教科書的な合成である。`3 ∤ a*b*c` を仮定すると、既存の
整数判別式補題が `3` 上の良還元を与え、局所トーション次数上界はその点の位数を
`2*3+1` 以下に抑える。一方、`p ≥ 5` なら `2*p > 7` なので矛盾する。

従ってここで閉じるのは、

`3 ∤ a*b*c  ⟹  hno`

という条件付きの残余表現入口である。一般の `hno`、全ての Frey 住所の処理、または
FLT の結論はこの定理の主張に含めない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/--
If `p ≥ 5`, `Even S.b`, and `3 ∤ a*b*c`, then no one-dimensional stable
cofixed residual line can exist.

The proof is intentionally short at the top level: the rational-torsion
construction supplies a point of exact order `2*p`; the integral good-reduction
bridge supplies the arithmetic hypothesis for the local bound; and the prime
`3` makes that bound equal to `7`. This is the textbook decomposition of the
`q = 3` obstruction, with no appeal to Mazur's classification.
-/
theorem residual_hno_of_three_good (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L := by
  exact S.residual_hno_of_small_good_prime hp5 hbe
    (q := 3) (by norm_num) (by omega) hd

end
end DkMath.FLT.Frey.Source
