/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoThreeGood

#print "file: DkMathTest.FLT.FreyHnoThreeGood"

namespace DkMathTest.FLT.FreyHnoThreeGood

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 教科書回帰例：`3` 上の良還元を、Cofixed 枝の `hno` 排除へ合成する。 -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L :=
  S.residual_hno_of_three_good hp5 hbe hd

#print axioms DkMath.FLT.Frey.Source.residual_hno_of_three_good

end
end DkMathTest.FLT.FreyHnoThreeGood
