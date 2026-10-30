/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalResidueField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

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

noncomputable local instance instDecidableEqFreyLocalValuationSubring {α : Type*} :
    DecidableEq α := Classical.decEq _

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

/-!
The residue-field functor is functorial for this local ring equivalence.  This
is the missing finite-field bridge: the two presentations of the local ring
have canonically equivalent residue fields, rather than merely residue fields
of the same cardinality.
-/

/-- The residue-field equivalence induced by the valuation-subring presentation. -/
noncomputable def localResidueFieldValuationSubringEquiv :
    IsLocalRing.ResidueField (LocalRing q) ≃+*
      IsLocalRing.ResidueField (localValuationSubring q) :=
  IsLocalRing.ResidueField.mapEquiv (localRingValuationSubringEquiv q)

@[simp]
theorem localResidueFieldValuationSubringEquiv_residue (x : LocalRing q) :
    localResidueFieldValuationSubringEquiv q (IsLocalRing.residue (LocalRing q) x) =
      IsLocalRing.residue (localValuationSubring q)
        (localRingValuationSubringEquiv q x) := by
  let : IsLocalHom (localRingValuationSubringEquiv q).toRingHom :=
    ⟨fun a ha => by
      have h' : IsUnit ((localRingValuationSubringEquiv q).symm
          (localRingValuationSubringEquiv q a)) := IsUnit.map
        (localRingValuationSubringEquiv q).symm ha
      simpa using h'⟩
  exact IsLocalRing.ResidueField.map_residue
    (localRingValuationSubringEquiv q).toRingHom x

/-!
Transporting the previously identified residue field of `LocalRing q` now
gives an explicit equivalence for the valuation-subring presentation.  The
finite and cardinality instances below are intentionally local to this
module; consumers can use the theorem without unfolding any construction.
-/

/-- The valuation-subring residue field is canonically `ZMod q`. -/
noncomputable def localValuationSubringResidueFieldEquiv :
    IsLocalRing.ResidueField (localValuationSubring q) ≃+* ZMod q :=
  (localResidueFieldValuationSubringEquiv q).symm.trans (localResidueFieldEquiv q)

noncomputable instance localValuationSubringResidueField_finite :
    Finite (IsLocalRing.ResidueField (localValuationSubring q)) :=
  Finite.of_equiv (ZMod q) (localValuationSubringResidueFieldEquiv q).symm.toEquiv

noncomputable instance localValuationSubringResidueField_fintype :
    Fintype (IsLocalRing.ResidueField (localValuationSubring q)) :=
  Fintype.ofFinite _

/-- The transported valuation-subring residue field has exactly `q` elements. -/
theorem localValuationSubringResidueField_card :
    Fintype.card (IsLocalRing.ResidueField (localValuationSubring q)) = q := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (localValuationSubringResidueFieldEquiv q).toEquiv, Nat.card_zmod]

/-- The equivalence embeds a localised integer as the same rational number. -/
theorem localRingValuationSubringEquiv_coe (x : LocalRing q) :
    ((localRingValuationSubringEquiv q x : localValuationSubring q) : ℚ) =
      algebraMap (LocalRing q) ℚ x := by
  rfl

/-- The transported valuation subring lies over the prime `q`. -/
theorem localValuationSubring_liesOverPrime :
    ValuationInertia.LiesOverPrime (localValuationSubring q) q := by
  let x : localValuationSubring q :=
    localRingValuationSubringEquiv q (algebraMap ℤ (LocalRing q) (q : ℤ))
  have hxcoe : (x : ℚ) = (q : ℚ) := by
    dsimp [x]
    rw [localRingValuationSubringEquiv_coe]
    rw [← IsScalarTower.algebraMap_apply ℤ (LocalRing q) ℚ]
    rfl
  change (q : ℚ) ∈ (localValuationSubring q).nonunits
  rw [← hxcoe]
  apply ValuationSubring.coe_mem_nonunits_iff.mpr
  by_contra hmem
  have hu : IsUnit x := (IsLocalRing.notMem_maximalIdeal).mp hmem
  have hu' := IsUnit.map (localRingValuationSubringEquiv q).symm hu
  have hnot : ¬ (q : ℤ) ∣ (q : ℤ) :=
    (isUnit_local_iff q (q : ℤ)).mp (by simpa [x] using hu')
  exact hnot dvd_rfl

/-- Transport an integral Weierstrass model to the valuation-subring presentation. -/
noncomputable def mapModelToValuationSubring
    (W : WeierstrassCurve (LocalRing q)) :
    WeierstrassCurve (localValuationSubring q) :=
  W.map (localRingValuationSubringEquiv q).toRingHom

/-- Discriminants of the two residue models correspond under the residue-field equivalence. -/
theorem mapModelToValuationSubring_residue_discriminant_map
    (W : WeierstrassCurve (LocalRing q)) :
    localResidueFieldValuationSubringEquiv q
        ((W.map (IsLocalRing.residue (LocalRing q))).Δ) =
      ((mapModelToValuationSubring q W).map
        (IsLocalRing.residue (localValuationSubring q))).Δ := by
  let : IsLocalHom (localRingValuationSubringEquiv q).toRingHom :=
    ⟨fun a ha => by
      have h' : IsUnit ((localRingValuationSubringEquiv q).symm
          (localRingValuationSubringEquiv q a)) := IsUnit.map
        (localRingValuationSubringEquiv q).symm ha
      simpa using h'⟩
  rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
  simp [mapModelToValuationSubring]

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
