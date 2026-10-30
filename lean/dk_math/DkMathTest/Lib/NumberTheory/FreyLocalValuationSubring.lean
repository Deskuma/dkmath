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

/-! The residue-field transport is an actual equivalence, not only a cardinality
statement.  This is the API consumed by the valuation-subring torsion bound. -/

noncomputable example :
    IsLocalRing.ResidueField (LocalRing q) ≃+*
      IsLocalRing.ResidueField (localValuationSubring q) :=
  localResidueFieldValuationSubringEquiv q

noncomputable example :
    IsLocalRing.ResidueField (localValuationSubring q) ≃+* ZMod q :=
  localValuationSubringResidueFieldEquiv q

example : Fintype.card (IsLocalRing.ResidueField (localValuationSubring q)) = q :=
  localValuationSubringResidueField_card q

example : (q : ℚ) ∈ (localValuationSubring q).nonunits :=
  localValuationSubring_liesOverPrime q

example (W : WeierstrassCurve (LocalRing q)) :
    localResidueFieldValuationSubringEquiv q
        ((W.map (IsLocalRing.residue (LocalRing q))).Δ) =
      ((mapModelToValuationSubring q W).map
        (IsLocalRing.residue (localValuationSubring q))).Δ :=
  mapModelToValuationSubring_residue_discriminant_map q W

#print axioms localRingValuationSubringEquiv
#print axioms localRingValuationSubringEquiv_coe
#print axioms mapModelToValuationSubring_map_subtype
#print axioms localResidueFieldValuationSubringEquiv
#print axioms localValuationSubringResidueFieldEquiv
#print axioms localValuationSubringResidueField_card
#print axioms localValuationSubring_liesOverPrime
#print axioms mapModelToValuationSubring_residue_discriminant_map

end
end DkMathTest.Lib.NumberTheory.FreyLocalValuationSubring
