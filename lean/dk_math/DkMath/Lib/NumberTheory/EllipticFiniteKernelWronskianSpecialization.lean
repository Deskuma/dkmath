/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelTwoTorsion
import DkMath.Lib.Algebra.WronskianCrossMultiplication

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization"

/-!
# Wronskian 局所評価の二捩れ入口

この層は、関数体上の Wronskian 恒等式そのものを再証明しない。
既存の `kernelXAt_translation`、`kernelYAt_translation`、`kernelYAt_neg` を
使い、源の二捩れ点を核の半代表で平行移動した点で、

`z_source ≠ 0` と `z_target = 0`

を別々に固定する。したがって、後続の点評価では「源では分母因子が非零」
と「標的の平方完成座標が零」を独立した入力として渡せる。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber
open scoped BigOperators

variable {K : Type*} [Field K] [NeZero (2 : K)]

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianSpecialization
    {α : Type*} : DecidableEq α := Classical.decEq _

omit [NeZero (2 : K)] in
/-- `genericX` is transcendental over the algebraic closure, by its double pole at `O`.

This is the coefficient-descent guard used when an equality of rational functions
is upgraded to an equality in `(AlgebraicClosure K)[X]`.  The proof uses only the
valuation of the Weierstrass x-coordinate at the point at infinity; it does not
assume that evaluation at an arbitrary function-field element is injective.
-/
theorem genericX_transcendental_for_wronskian
    (E : WeierstrassCurve K) [E.IsElliptic] :
    Transcendental (AlgebraicClosure K) (genericX E (AlgebraicClosure K)) := by
  apply transcendental_of_point_pole E 0
  change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point)
    (genericX E (AlgebraicClosure K))
  rw [pointValuation_zero_genericX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

omit [NeZero (2 : K)] in
/-- Every base-coefficient polynomial in `genericX` is regular at a finite point.

The proof is the valuation-theoretic form of polynomial substitution: `genericX`
is congruent to the point's x-coordinate, and `Valuation.Cong.eval₂` propagates
that congruence through the polynomial.  This lemma is the basic regularity
input for evaluating the base Vélu numerator, denominator, and Wronskian.
-/
theorem pointValuation_aeval_le_one
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E) (hP : P ≠ 0) (p : (AlgebraicClosure K)[X]) :
    pointValuation E P
        (Polynomial.aeval (genericX E (AlgebraicClosure K)) p) ≤ 1 := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let x := genericX E (AlgebraicClosure K)
  have hc : ∀ c : AlgebraicClosure K,
      pointValuation E P (algebraMap (AlgebraicClosure K) F c) ≤ 1 := by
    intro c
    exact pointValuation_const_le_one E P c
  have hxc : (pointValuation E P).Cong x
      (algebraMap (AlgebraicClosure K) F P.xc) := by
    have h := value_spec E P x (pointValuation_genericX_le_one E P hP)
    rw [value_genericX E P hP] at h
    exact h
  have hh := (Valuation.Cong.eval₂ (algebraMap (AlgebraicClosure K) F)
    hc hxc (hc P.xc) p).1
  rw [eval₂_at_apply] at hh
  exact hh.le_one (hc _)

omit [NeZero (2 : K)] in
/-- The finite value of a base polynomial is its ordinary x-coordinate evaluation. -/
theorem value_aeval_eq_eval
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E) (hP : P ≠ 0) (p : (AlgebraicClosure K)[X]) :
    value E P (Polynomial.aeval (genericX E (AlgebraicClosure K)) p)
        (pointValuation_aeval_le_one E P hP p) = p.eval P.xc := by
  apply value_eq
  have hc : ∀ c : AlgebraicClosure K,
      pointValuation E P (algebraMap (AlgebraicClosure K)
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
    intro c
    exact pointValuation_const_le_one E P c
  have hxc : (pointValuation E P).Cong (genericX E (AlgebraicClosure K))
      (algebraMap (AlgebraicClosure K)
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField P.xc) := by
    have h := value_spec E P (genericX E (AlgebraicClosure K))
      (pointValuation_genericX_le_one E P hP)
    rw [value_genericX E P hP] at h
    exact h
  have hh := (Valuation.Cong.eval₂
    (algebraMap (AlgebraicClosure K)
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    hc hxc (hc P.xc) p).1
  rw [eval₂_at_apply] at hh
  exact hh

omit [NeZero (2 : K)] in
/-- The base-field common denominator is non-zero at the generic x-coordinate.

Each finite-product factor is a square of `genericX - x(Q)`.  The generic
coordinate is transcendental, hence cannot equal the algebraic x-coordinate of
any half-kernel representative.  This is the function-field counterpart of
the finite-point collision lemma proved below.
-/
theorem veluHalfDenominatorBase_eval_genericX_ne_zero
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H] :
    Polynomial.aeval (genericX E (AlgebraicClosure K))
      (veluHalfDenominatorBase E H) ≠ 0 := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  simp only [map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun Q hQ => by
    simp only [xCorrectionDenominator, map_mul, map_sub, aeval_X, aeval_C]
    exact mul_ne_zero (sub_ne_zero.mpr (genericX_ne_const E Q.val.xc))
      (sub_ne_zero.mpr (genericX_ne_const E Q.val.xc)))

omit [NeZero (2 : K)] in
/-- The function-field Vélu quotient can be read from the base-coefficient pair.

`map_veluHalfNumeratorBase` and `map_veluHalfDenominatorBase` identify the
coefficient images.  `eval_map_algebraMap` then turns evaluation of those images
back into `aeval` of the algebraic-closure polynomials, so the quotient is
available in exactly the coefficient type required by `cross_relation_of_aeval_div_eq`.
-/
theorem veluX_eq_veluHalfNumeratorBase_div_denominator
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K))
        (veluHalfNumeratorBase E H) /
        Polynomial.aeval (genericX E (AlgebraicClosure K))
          (veluHalfDenominatorBase E H) := by
  have h := veluX_eq_veluHalfNumerator_div_denominator E H ho
  have hN := map_veluHalfNumeratorBase E H
  have hD := map_veluHalfDenominatorBase E H
  dsimp only at hN hD
  rw [← hN, ← hD] at h
  simpa only [eval_map_algebraMap] using h

omit [NeZero (2 : K)] in
/-- A standard `RatFunc` presentation cross-multiplies with the base Vélu pair.

The two quotient presentations of `veluX` are first aligned in the function
field.  `genericX_transcendental_for_wronskian` and
`cross_relation_of_aeval_div_eq` then turn that evaluated equality into the
polynomial identity required for Wronskian transport.  The denominator guard is
kept explicit rather than being inferred from a formal fraction.
-/
theorem veluX_standard_pair_cross_relation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G) :
    F * veluHalfDenominatorBase E H =
      veluHalfNumeratorBase E H * G := by
  let x := genericX E (AlgebraicClosure K)
  have hD : Polynomial.aeval x (veluHalfDenominatorBase E H) ≠ 0 := by
    simpa [x] using veluHalfDenominatorBase_eval_genericX_ne_zero E H
  have hbase := veluX_eq_veluHalfNumeratorBase_div_denominator E H ho
  have hfrac : Polynomial.aeval x F / Polynomial.aeval x G =
      Polynomial.aeval x (veluHalfNumeratorBase E H) /
        Polynomial.aeval x (veluHalfDenominatorBase E H) := by
    calc
      Polynomial.aeval x F / Polynomial.aeval x G = veluX E H := by
        simpa [x] using hrel.symm
      _ = Polynomial.aeval x (veluHalfNumeratorBase E H) /
          Polynomial.aeval x (veluHalfDenominatorBase E H) := by
        simpa [x] using hbase
  exact cross_relation_of_aeval_div_eq F G (veluHalfNumeratorBase E H)
    (veluHalfDenominatorBase E H) x
    (genericX_transcendental_for_wronskian E) hG hD hfrac

omit [NeZero (2 : K)] in
/-- 源曲線上で、有限点の平方完成座標が零なら反転固定点になる。 -/
theorem eq_neg_of_completedSquare_eq_zero
    (E : WeierstrassCurve K) (P : Points E) (hP : P ≠ 0)
    (hz : 2 * P.yc + (E⁄(AlgebraicClosure K)).a₁ * P.xc +
        (E⁄(AlgebraicClosure K)).a₃ = 0) :
    -P = P := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hns =>
      change -(Point.some x y hns : (E⁄(AlgebraicClosure K)).Point) =
        (Point.some x y hns : (E⁄(AlgebraicClosure K)).Point)
      rw [Affine.Point.neg_some, Affine.Point.some.injEq]
      constructor
      · rfl
      · dsimp only [Affine.negY]
        change -y - (E⁄(AlgebraicClosure K)).a₁ * x -
          (E⁄(AlgebraicClosure K)).a₃ = y
        change 2 * y + (E⁄(AlgebraicClosure K)).a₁ * x +
          (E⁄(AlgebraicClosure K)).a₃ = 0 at hz
        linear_combination -hz

omit [NeZero (2 : K)] in
/-- 反転非固定な有限点では、源の平方完成座標は非零である。 -/
theorem completedSquare_ne_zero_of_neg_ne
    (E : WeierstrassCurve K) (P : Points E) (hP : P ≠ 0)
    (hneg : -P ≠ P) :
    2 * P.yc + (E⁄(AlgebraicClosure K)).a₁ * P.xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0 := by
  intro hz
  exact hneg (eq_neg_of_completedSquare_eq_zero E P hP hz)

/-- 核外の源二捩れ点は、標的側の平方完成座標を零に送る。 -/
theorem kernelAt_completedSquare_eq_zero_of_neg_fixed
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    2 * kernelYAt E H P hP + (kernelModel E H).a₁ * kernelXAt E H P hP +
        (kernelModel E H).a₃ = 0 := by
  have hy := kernelYAt_neg E H P hP
  have hy' : kernelYAt E H P hP =
      -kernelYAt E H P hP - (E⁄(AlgebraicClosure K)).a₁ * kernelXAt E H P hP -
        (E⁄(AlgebraicClosure K)).a₃ := by
    simpa only [hneg] using hy
  rw [kernelModel_a₁, kernelModel_a₃]
  linear_combination hy'

/-- 二捩れ点を半核代表で移動しても、標的の平方完成座標は零である。 -/
theorem kernelAt_completedSquare_eq_zero_of_neg_fixed_translation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) :
    2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0 := by
  rw [kernelYAt_translation E H P hP Q,
    kernelXAt_translation E H P hP Q]
  exact kernelAt_completedSquare_eq_zero_of_neg_fixed E H P hP hneg

/-! `T + Q` は核の外に残るので、源側の平方完成座標へも同じ点評価 API を
適用できる。ここでは `T + Q` が反転固定でないことを仮定として明示する。
奇数核からこの仮定を供給する群論補題は、核の位数条件を扱う別層に残す。 -/

omit [NeZero (2 : K)] in
/-- 核外の点を核点で移動したとき、源側の平方完成座標が非零なら
標的側の平方完成座標零性と同じ軌道で利用できる。 -/
theorem completedSquare_ne_zero_of_neg_ne_translation
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E))
    (P : Points E) (hP : P ∉ H) (Q : H)
    (hneg : -(P + Q.val) ≠ P + Q.val) :
    2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0 := by
  apply completedSquare_ne_zero_of_neg_ne E (P + Q.val) ?_ hneg
  intro hz
  apply hP
  rw [eq_neg_of_add_eq_zero_left hz]
  exact H.neg_mem Q.property

omit [NeZero (2 : K)] in
/-- 奇数位数の核では、非零核点を二捩れ点へ加えても反転固定にはならない。
反転固定を仮定すると、二捩れ点の差である核点自身も反転固定になり、
`eq_zero_of_mem_odd_kernel_fixed` により零点へ落ちる。 -/
theorem neg_ne_of_odd_kernel_twoTorsion_translate
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E))
    (hodd : Odd (Nat.card H))
    (P : Points E) (hneg : -P = P) (Q : H) (hQ : Q ≠ 0) :
    -(P + Q.val) ≠ P + Q.val := by
  intro hnegTranslation
  have htwoP : P + P = 0 := by
    simpa only [hneg] using add_neg_cancel P
  have htwoPQ : (P + Q.val) + (P + Q.val) = 0 := by
    simpa only [hnegTranslation] using add_neg_cancel (P + Q.val)
  have htwoQ : Q.val + Q.val = 0 := by
    calc
      Q.val + Q.val = (P + Q.val) + (P + Q.val) - (P + P) := by abel
      _ = 0 - 0 := by rw [htwoPQ, htwoP]
      _ = 0 := sub_self 0
  have hnegQ : -Q.val = Q.val :=
    (eq_neg_of_add_eq_zero_left htwoQ).symm
  have hQval : Q.val = 0 :=
    eq_zero_of_mem_odd_kernel_fixed E H hodd Q.val Q.property hnegQ
  apply hQ
  exact Subtype.ext hQval

omit [NeZero (2 : K)] in
/-- 基礎係数体側の共通分母は、評価点のx座標が各半核代表と衝突しなければ
非零である。これは後続の Wronskian 恒等式を点へ特殊化する際の分母条件を、
有限積の各因子へ分解した形で供給する。 -/
theorem veluHalfDenominatorBase_eval_ne_zero
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (R : Points E) (hcollision : ∀ Q : halfKernel E H,
      R.xc ≠ Q.val.val.xc) :
    (veluHalfDenominatorBase E H).eval R.xc ≠ 0 := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro Q hQ
  simp only [xCorrectionDenominator, eval_mul, eval_sub, eval_X, eval_C]
  exact mul_ne_zero
    (sub_ne_zero.mpr (hcollision ⟨Q, hQ⟩))
    (sub_ne_zero.mpr (hcollision ⟨Q, hQ⟩))

omit [NeZero (2 : K)] in
/-- 核外点を核点で移動した点の x 座標は、半核のどの代表とも衝突しない。
同じ x 座標なら有限点は同一点か反転対であり、いずれの場合も `P ∈ H` を
導くため、核外仮定に反する。 -/
theorem translated_x_ne_halfKernel_of_kernel_outside
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) (S : halfKernel E H) :
    (P + Q.val).xc ≠ S.val.val.xc := by
  intro hx
  have hR : P + Q.val ≠ 0 := by
    intro hzero
    apply hP
    rw [eq_neg_of_add_eq_zero_left hzero]
    exact H.neg_mem Q.property
  have hS : S.val.val ≠ 0 := by
    intro hzero
    have hsub : S.val = 0 := Subtype.ext hzero
    exact ((mem_halfKernel E H S.val).mp S.property).1 hsub
  rcases point_eq_or_eq_neg_of_xc_eq E (P + Q.val) S.val.val hR hS hx with he | he
  · apply hP
    have hp0 : P = S.val.val - Q.val := by
      calc
        P = (P + Q.val) - Q.val := by abel
        _ = S.val.val - Q.val := by rw [he]
    rw [hp0]
    exact H.sub_mem S.val.property Q.property
  · apply hP
    have hp0 : P = -S.val.val - Q.val := by
      calc
        P = (P + Q.val) - Q.val := by abel
        _ = -S.val.val - Q.val := by rw [he]
    rw [hp0]
    exact H.sub_mem (H.neg_mem S.val.property) Q.property

omit [NeZero (2 : K)] in
/-- 前の衝突排除を有限積へ適用した、翻訳点での基礎共通分母非零性。 -/
theorem veluHalfDenominatorBase_eval_ne_zero_translation
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) :
    (veluHalfDenominatorBase E H).eval (P + Q.val).xc ≠ 0 := by
  apply veluHalfDenominatorBase_eval_ne_zero E H (P + Q.val)
  intro S
  exact translated_x_ne_halfKernel_of_kernel_outside E H P hP Q S

omit [NeZero (2 : K)] in
/-- Transport a base-pair Wronskian root to any translated kernel point.

The cross relation is supplied by the standard `veluX` quotient, while the
finite denominator is discharged by the x-coordinate collision lemma for
`P + Q`.  Thus the only geometric input left to the caller is the Wronskian
root for the base pair itself.
-/
theorem veluX_standard_pair_wronskian_root_of_translation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (P : Points E) (hP : P ∉ H) (Q : H)
    (hbase :
      (wronskian (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H)).IsRoot (P + Q.val).xc) :
    (wronskian F G).IsRoot (P + Q.val).xc := by
  apply wronskian_isRoot_of_cross_relation F G
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H)
    (P + Q.val).xc
    (veluX_standard_pair_cross_relation E H ho F G hG hrel)
    (veluHalfDenominatorBase_eval_ne_zero_translation E H P hP Q)
    hbase

/-- Extract the base-pair Wronskian root from a cleared identity at `P + Q`.

The odd-kernel two-torsion packet supplies the two scalar facts
`z_source ≠ 0` and `z_target = 0`.  The remaining hypothesis is precisely the
point-specialized, denominator-cleared Vélu identity; keeping it explicit
marks the boundary where regular evaluation of the function-field identity
must still be proved.
-/
theorem veluHalf_base_wronskian_root_of_cleared_identity
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0)
    (hidentity :
      (veluHalfDenominatorBase E H).eval (P + Q.val).xc ^ 2 *
          (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
            (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
              (add_not_mem_kernel E H P hP Q) + (kernelModel E H).a₃) =
        (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
            (E⁄(AlgebraicClosure K)).a₃) *
          (wronskian (veluHalfNumeratorBase E H)
            (veluHalfDenominatorBase E H)).eval (P + Q.val).xc) :
    (wronskian (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).IsRoot (P + Q.val).xc := by
  have hnegTranslation := neg_ne_of_odd_kernel_twoTorsion_translate
    E H ho P hneg Q hQ
  have hz := completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hnegTranslation
  have hzH := kernelAt_completedSquare_eq_zero_of_neg_fixed_translation
    E H P hP hneg Q
  exact wronskian_isRoot_of_denominator_cleared_identity
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H)
    (P + Q.val).xc
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
      (E⁄(AlgebraicClosure K)).a₃)
    (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
      (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
        (add_not_mem_kernel E H P hP Q) + (kernelModel E H).a₃)
    hidentity hz hzH

/-! 点評価へ渡す最小の「源非零・標的零」パケット。 -/

theorem completedSquare_translation_pair
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H)
    (hnegTranslation : -(P + Q.val) ≠ P + Q.val) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) := by
  constructor
  · exact completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hnegTranslation
  · exact kernelAt_completedSquare_eq_zero_of_neg_fixed_translation E H P hP hneg Q

/-- 奇数核の非零点を半核代表として選んだ場合の、局所評価パケットの
仮定を `hnegTranslation` なしで供給する公開版。 -/
theorem completedSquare_translation_pair_of_odd_kernel
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) (hQ : Q ≠ 0) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) := by
  exact completedSquare_translation_pair E H P hP hneg Q
    (neg_ne_of_odd_kernel_twoTorsion_translate E H hodd P hneg Q hQ)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
