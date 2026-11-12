/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalReduction
import DkMath.Lib.NumberTheory.FiniteFieldWeierstrassCard
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Int

#print "file: DkMath.Lib.NumberTheory.FreyLocalResidueField"

/-!
# NOTE-032: 局所整数環の剰余体を有限素体へ固定する

`FreyLocalReduction.LocalRing q` は、素数 `q` での整数の局所化である。
有限体上の点数評価へ進むには、その剰余体を代数閉包として扱ってはならない。
このファイルでは、整数の商

`ℤ ⧸ (q) ≃+* ZMod q`

と、局所環から剰余体への自然な写像の全単射性を組み合わせ、

`ResidueField (LocalRing q) ≃+* ZMod q`

を構成する。以後の有限体評価は、この同値と `localResidueField_card` を
明示的に消費する。
-/

namespace DkMath.Lib.NumberTheory.FreyLocalReduction

open DkMath.Lib.NumberTheory

noncomputable section

noncomputable local instance instDecidableEqFreyLocalResidueField {α : Type*} : DecidableEq α :=
  Classical.decEq _

variable (q : ℕ) [Fact q.Prime]

/--
`LocalRing q` の剰余体を `ZMod q` と同一視する環同値。

教科書的には、まず `ℤ/(q)` と `ZMod q` の標準同値を取り、次に
局所化の剰余体への商写像
`algebraMap (ℤ/(q)) (ResidueField (LocalRing q))`
が、極大イデアル性により全単射になることを使う。
この順序により、有限体の大きさを「局所化の直観」ではなく、
明示的な商環の計算として固定している。
-/
noncomputable def localResidueFieldEquiv :
    IsLocalRing.ResidueField (LocalRing q) ≃+* ZMod q := by
  letI : (primeIdeal q).IsMaximal := by
    unfold primeIdeal
    exact Int.ideal_span_isMaximal_of_prime q
  let eQ : (ℤ ⧸ primeIdeal q) ≃+* ZMod q := by
    change (ℤ ⧸ Ideal.span {(q : ℤ)}) ≃+* ZMod q
    exact Int.quotientSpanNatEquivZMod q
  let eR : (ℤ ⧸ primeIdeal q) ≃+*
      IsLocalRing.ResidueField (LocalRing q) :=
    RingEquiv.ofBijective (algebraMap (ℤ ⧸ primeIdeal q)
      (IsLocalRing.ResidueField (LocalRing q)))
      (Ideal.bijective_algebraMap_quotient_residueField (primeIdeal q))
  exact eR.symm.trans eQ

/-- The local residue field is finite because it is ring-isomorphic to `ZMod q`. -/
noncomputable instance localResidueField_finite :
    Finite (IsLocalRing.ResidueField (LocalRing q)) :=
  Finite.of_equiv (ZMod q) (localResidueFieldEquiv q).symm.toEquiv

/-- A canonical finite type structure transported from `ZMod q`. -/
noncomputable instance localResidueField_fintype :
    Fintype (IsLocalRing.ResidueField (LocalRing q)) :=
  Fintype.ofFinite _

/-- The cardinality of the local residue field is exactly the prime `q`. -/
theorem localResidueField_natCard :
    Nat.card (IsLocalRing.ResidueField (LocalRing q)) = q := by
  rw [Nat.card_congr (localResidueFieldEquiv q).toEquiv, Nat.card_zmod]

/-- The `Fintype.card` form of `localResidueField_natCard`. -/
theorem localResidueField_card :
    Fintype.card (IsLocalRing.ResidueField (LocalRing q)) = q := by
  rw [← Nat.card_eq_fintype_card, localResidueField_natCard]

/--
The residue-field equivalence respects reduction of integers.

This is the commuting square needed when an integral Weierstrass model is
reduced at `q`: an integer first mapped to the local ring and then reduced
has the same image as its usual class in `ZMod q`.
-/
theorem localResidueFieldEquiv_comp_algebraMap :
    (localResidueFieldEquiv q :
      IsLocalRing.ResidueField (LocalRing q) →+* ZMod q).comp
        (algebraMap ℤ (IsLocalRing.ResidueField (LocalRing q))) =
      Int.castRingHom (ZMod q) := by
  ext z
  change localResidueFieldEquiv q
      (algebraMap ℤ (IsLocalRing.ResidueField (LocalRing q)) z) = _
  simp [localResidueFieldEquiv]

/--
The elementary point-count bound is now available for the actual local
residue model.  The only geometric input is non-vanishing of its reduced
discriminant; all arithmetic content is the preceding cardinality theorem.
-/
theorem localResidue_weierstrass_points_card_le_two_mul_prime_add_one
    (W : WeierstrassCurve (LocalRing q))
    (hgood : (W.map (IsLocalRing.residue (LocalRing q))).Δ ≠ 0) :
    Nat.card (W.map (IsLocalRing.residue (LocalRing q))).toAffine.Point ≤
      2 * q + 1 := by
  let W₀ := W.map (IsLocalRing.residue (LocalRing q))
  let : W₀.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hgood⟩
  let : Fintype {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2} :=
    Fintype.ofFinite _
  let : Finite (WithZero {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2}) := by
    change Finite (Option {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2})
    infer_instance
  let : Fintype (WithZero {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2}) :=
    Fintype.ofFinite _
  let : Fintype W₀.toAffine.Point := Fintype.ofEquiv _ W₀.toAffine.pointEquiv.symm
  have h := card_weierstrass_points_le_two_mul_card_add_one W₀
  rw [localResidueField_card] at h
  simpa [W₀] using h

/--
An abstract valuation-ring version of the prime-sized torsion bound.

The reduction theorem only needs a finite residue field.  Supplying an
explicit ring equivalence with `ZMod q` turns its cardinality parameter into
the arithmetic prime `q`, while preserving the smooth-reduction hypotheses
and the unit-valuation condition.  This is the reusable bridge for any
local model whose residue field has been identified with `𝔽_q`.
-/
theorem finite_smooth_torsion_ncard_le_two_mul_prime_add_one_of_residueEquiv
    {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L)
    (W : WeierstrassCurve A)
    [Finite (IsLocalRing.ResidueField A)] {q : ℕ} [Fact q.Prime]
    (e : IsLocalRing.ResidueField A ≃+* ZMod q)
    (hgood : (W.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hn : A.valuation (n : L) = 1) :
    {P : (W.map A.subtype).toAffine.Point |
        EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point |
        EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.ncard ≤
        2 * q + 1 := by
  classical
  let : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  have hcard : Fintype.card (IsLocalRing.ResidueField A) = q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv, Nat.card_zmod]
  have h := finite_smooth_torsion_ncard_le_two_mul_residue_card_add_one A W hgood hn
  simpa [hcard] using h

/--
The same specialization excludes an exact `2 * p`-torsion point in the local
residue model whenever `q < p`.  This is deliberately a theorem about the
`ZMod q`-fiber itself: the missing arithmetic step is the transport of a
rational torsion point into this fiber, not the finite-field contradiction.
-/
theorem no_two_mul_order_of_localResidue_weierstrass_of_prime
    (W : WeierstrassCurve (LocalRing q))
    [hEll : (W.map (IsLocalRing.residue (LocalRing q))).IsElliptic]
    {p : ℕ} (hqp : q < p) :
    ¬ ∃ Q : (W.map (IsLocalRing.residue (LocalRing q))).toAffine.Point,
      addOrderOf Q = 2 * p := by
  let W₀ := W.map (IsLocalRing.residue (LocalRing q))
  let : Fintype {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2} :=
    Fintype.ofFinite _
  let : Finite (WithZero {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2}) := by
    change Finite (Option {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2})
    infer_instance
  let : Fintype (WithZero {xy : IsLocalRing.ResidueField (LocalRing q) ×
      IsLocalRing.ResidueField (LocalRing q) // W₀.toAffine.Equation xy.1 xy.2}) :=
    Fintype.ofFinite _
  let : Fintype W₀.toAffine.Point := Fintype.ofEquiv _ W₀.toAffine.pointEquiv.symm
  change ¬ ∃ Q : W₀.toAffine.Point, addOrderOf Q = 2 * p
  apply no_two_mul_order_of_weierstrass_of_card_le W₀ (localResidueField_card q).le hqp

end
end DkMath.Lib.NumberTheory.FreyLocalReduction
