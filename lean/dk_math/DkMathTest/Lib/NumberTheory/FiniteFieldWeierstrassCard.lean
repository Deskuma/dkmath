/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.FiniteFieldWeierstrassCard

#print "file: DkMathTest.Lib.NumberTheory.FiniteFieldWeierstrassCard"

namespace DkMathTest.Lib.NumberTheory.FiniteFieldWeierstrassCard

open DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [Fintype K]

noncomputable local instance instDecidableEqFiniteFieldWeierstrassCardTest {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- 教科書回帰例：有限体上の固定 `x` ファイバーは高々二点。 -/
example (W : WeierstrassCurve K) [W.IsElliptic] (x : K) :
    (nonzeroXFiber W x).ncard ≤ 2 :=
  nonzeroXFiber_ncard_le_two W x

/-- 教科書回帰例：有限体 Weierstrass 点数の初等上界。 -/
example (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card W.toAffine.Point ≤ 2 * Fintype.card K + 1 :=
  card_weierstrass_points_le_two_mul_card_add_one W

/-- 教科書回帰例：単射加法準同型は点の位数を標的個数で抑える。 -/
example {G H : Type*} [AddGroup G] [AddGroup H] [Finite H]
    (f : G →+ H) (hf : Function.Injective f) (Q : G) :
    addOrderOf Q ≤ Nat.card H :=
  addOrderOf_le_natCard_of_injective_addMonoidHom f hf Q

/-- 教科書回帰例：点数上界が `2 * p` より小さければ、その位数は排除される。 -/
example (W : WeierstrassCurve K) [W.IsElliptic] {p : ℕ}
    (hsmall : 2 * Fintype.card K + 1 < 2 * p) :
    ¬ ∃ Q : W.toAffine.Point, addOrderOf Q = 2 * p :=
  no_two_mul_order_of_weierstrass_of_card_lt W hsmall

/-- 教科書回帰例：剰余体濃度 `≤ q < p` という算術条件を使う。 -/
example (W : WeierstrassCurve K) [W.IsElliptic] {p q : ℕ}
    (hcard : Fintype.card K ≤ q) (hqp : q < p) :
    ¬ ∃ Q : W.toAffine.Point, addOrderOf Q = 2 * p :=
  no_two_mul_order_of_weierstrass_of_card_le W hcard hqp

noncomputable example {L : Type*} [Field L] [CharZero L]
    (A : ValuationSubring L) (W : WeierstrassCurve A)
    [Fintype (IsLocalRing.ResidueField A)]
    (hgood : (W.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hn : A.valuation (n : L) = 1) :
    {P : (W.map A.subtype).toAffine.Point |
        DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point |
        DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation.HasSmoothReduction W P ∧ n • P = 0}.ncard ≤
        2 * Fintype.card (IsLocalRing.ResidueField A) + 1 :=
  finite_smooth_torsion_ncard_le_two_mul_residue_card_add_one A W hgood hn

#print axioms DkMath.Lib.NumberTheory.card_weierstrass_points_le_two_mul_card_add_one
#print axioms DkMath.Lib.NumberTheory.addOrderOf_le_natCard_of_injective_addMonoidHom
#print axioms DkMath.Lib.NumberTheory.addOrderOf_le_two_mul_card_add_one_of_weierstrass
#print axioms DkMath.Lib.NumberTheory.no_two_mul_order_of_weierstrass_of_card_lt
#print axioms DkMath.Lib.NumberTheory.no_two_mul_order_of_weierstrass_of_card_le
#print axioms DkMath.Lib.NumberTheory.finite_smooth_torsion_ncard_le_two_mul_residue_card_add_one

end DkMathTest.Lib.NumberTheory.FiniteFieldWeierstrassCard
