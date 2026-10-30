/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalResidueField

#print "file: DkMath.Lib.NumberTheory.FreyLocalValuationSubring"

/-!
# NOTE-032: `LocalRing q` と有理数体の付値部分環を接続する

`FreyLocalReduction.LocalRing q` は局所化として構成され、滑らかな捩れ還元 API は
`ValuationSubring ℚ` を係数環として受け取る。Mathlib の DVR 同値
`IsDiscreteValuationRing.equivValuationSubring` により、この二つの表現を同じ
`q`-進付値から直接接続する。

ここで証明するのは型の輸送と係数写像の可換性である。剰余体同値や捩れ点の具体的な
局所積分性を、この段階で自動的に仮定してはいない。
-/

namespace DkMath.Lib.NumberTheory.FreyLocalReduction

noncomputable section

variable (q : ℕ) [Fact q.Prime]

/-- The valuation subring of `ℚ` attached to the maximal ideal of `LocalRing q`. -/
noncomputable def localValuationSubring : ValuationSubring ℚ :=
  ((IsDiscreteValuationRing.maximalIdeal (LocalRing q)).valuation ℚ).valuationSubring

/--
The localised integer ring and its valuation-subring presentation are ring-isomorphic.

The right-hand side is exactly the valuation subring associated with the DVR valuation
on `LocalRing q`; no completion or algebraic closure is introduced.
-/
noncomputable def localRingValuationSubringEquiv :
    LocalRing q ≃+* localValuationSubring q :=
  IsDiscreteValuationRing.equivValuationSubring

/-- The equivalence embeds a localised integer as the same rational number. -/
theorem localRingValuationSubringEquiv_coe (x : LocalRing q) :
    ((localRingValuationSubringEquiv q x : localValuationSubring q) : ℚ) =
      algebraMap (LocalRing q) ℚ x := by
  rfl

/-- Transport an integral Weierstrass model to the valuation-subring presentation. -/
noncomputable def mapModelToValuationSubring
    (W : WeierstrassCurve (LocalRing q)) :
    WeierstrassCurve (localValuationSubring q) :=
  W.map (localRingValuationSubringEquiv q).toRingHom

/--
After transporting coefficients, base change to `ℚ` is the same as base change from
the original localised model.  This is the coefficient-level bridge needed before
transporting points and smooth-reduction predicates.
-/
theorem mapModelToValuationSubring_map_subtype
    (W : WeierstrassCurve (LocalRing q)) :
    (mapModelToValuationSubring q W).map (localValuationSubring q).subtype =
      W.map (algebraMap (LocalRing q) ℚ) := by
  ext <;> rfl

end
end DkMath.Lib.NumberTheory.FreyLocalReduction
