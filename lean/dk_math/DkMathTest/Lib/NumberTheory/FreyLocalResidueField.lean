/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyLocalResidueField

#print "file: DkMathTest.Lib.NumberTheory.FreyLocalResidueField"

namespace DkMathTest.Lib.NumberTheory.FreyLocalResidueField

open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.FreyLocalReduction
open WeierstrassCurve

noncomputable local instance instDecidableEqFreyLocalResidueFieldTest {α : Type*} :
    DecidableEq α := Classical.decEq _

variable (q : ℕ) [Fact q.Prime]

/-- 教科書回帰例：局所化の剰余体は `ZMod q` と環同値である。 -/
noncomputable example :
    IsLocalRing.ResidueField (LocalRing q) ≃+* ZMod q :=
  localResidueFieldEquiv q

/-- 教科書回帰例：剰余体の濃度は局所化した素数そのものである。 -/
example : Fintype.card (IsLocalRing.ResidueField (LocalRing q)) = q :=
  localResidueField_card q

/-- 教科書回帰例：整数の還元は `ZMod q` の通常の剰余と可換する。 -/
example :
    (localResidueFieldEquiv q :
      IsLocalRing.ResidueField (LocalRing q) →+* ZMod q).comp
        (algebraMap ℤ (IsLocalRing.ResidueField (LocalRing q))) =
      Int.castRingHom (ZMod q) :=
  localResidueFieldEquiv_comp_algebraMap q

/-- 教科書回帰例：局所化の実際の剰余モデルにも `2q+1` 点数上界が移る。 -/
example (W : WeierstrassCurve (LocalRing q))
    (hgood : (W.map (IsLocalRing.residue (LocalRing q))).Δ ≠ 0) :
    Nat.card (W.map (IsLocalRing.residue (LocalRing q))).toAffine.Point ≤
      2 * q + 1 :=
  localResidue_weierstrass_points_card_le_two_mul_prime_add_one q W hgood

/-- 教科書回帰例：剰余体同値を与えれば、抽象局所定理の上界を `2q+1` に固定できる。 -/
noncomputable example {L : Type*} [Field L] [CharZero L]
    (A : ValuationSubring L) (W : WeierstrassCurve A)
    [Fintype (IsLocalRing.ResidueField A)]
    {q : ℕ} [Fact q.Prime]
    (e : IsLocalRing.ResidueField A ≃+* ZMod q)
    (hgood : (W.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hn : A.valuation (n : L) = 1) :
    {P : (W.map A.subtype).toAffine.Point |
        DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point |
        DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.ncard ≤
        2 * q + 1 :=
  finite_smooth_torsion_ncard_le_two_mul_prime_add_one_of_residueEquiv
    A W e hgood hn

/-- 教科書回帰例：`q < p` なら局所剰余モデルに厳密位数 `2p` の点はない。 -/
example (W : WeierstrassCurve (LocalRing q))
    [hEll : (W.map (IsLocalRing.residue (LocalRing q))).IsElliptic]
    {p : ℕ} (hqp : q < p) :
    ¬ ∃ Q : (W.map (IsLocalRing.residue (LocalRing q))).toAffine.Point,
      addOrderOf Q = 2 * p :=
  no_two_mul_order_of_localResidue_weierstrass_of_prime q W hqp

#print axioms localResidueFieldEquiv
#print axioms localResidueField_natCard
#print axioms localResidueField_card
#print axioms localResidueFieldEquiv_comp_algebraMap
#print axioms localResidue_weierstrass_points_card_le_two_mul_prime_add_one
#print axioms finite_smooth_torsion_ncard_le_two_mul_prime_add_one_of_residueEquiv
#print axioms no_two_mul_order_of_localResidue_weierstrass_of_prime

end DkMathTest.Lib.NumberTheory.FreyLocalResidueField
