/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalValuationSubring

#print "file: DkMathTest.Lib.NumberTheory.FreyLocalValuationSubring"

namespace DkMathTest.Lib.NumberTheory.FreyLocalValuationSubring

open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.FreyLocalReduction

noncomputable section

variable (q : ℕ) [Fact q.Prime]

/-- 教科書回帰例：局所化環は有理数体の付値部分環へ環同値で移る。 -/
noncomputable example :
    LocalRing q ≃+* localValuationSubring q :=
  localRingValuationSubringEquiv q

/-- 教科書回帰例：係数の有理数への埋込みは輸送前後で一致する。 -/
example (x : LocalRing q) :
    ((localRingValuationSubringEquiv q x : localValuationSubring q) : ℚ) =
      algebraMap (LocalRing q) ℚ x :=
  localRingValuationSubringEquiv_coe q x

/-- 教科書回帰例：Weierstrass モデルの有理数体への基底変換が可換する。 -/
example (W : WeierstrassCurve (LocalRing q)) :
    (mapModelToValuationSubring q W).map (localValuationSubring q).subtype =
      W.map (algebraMap (LocalRing q) ℚ) :=
  mapModelToValuationSubring_map_subtype q W

#print axioms localRingValuationSubringEquiv
#print axioms localRingValuationSubringEquiv_coe
#print axioms mapModelToValuationSubring_map_subtype

end
end DkMathTest.Lib.NumberTheory.FreyLocalValuationSubring
