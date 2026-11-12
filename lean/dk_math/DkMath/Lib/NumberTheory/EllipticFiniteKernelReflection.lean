/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelGeneration
import DkMath.Lib.NumberTheory.EllipticFunctionFieldNegation
import DkMath.Lib.Algebra.QuadraticFixedField

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelReflection"

/-!
# 核の正規化和を反射すると、同じWeierstrass反転になる

[DkMath.Lib] X_Hは反転で固定され、Y_Hは−Y_H−a₁X_H−a₃に移る。
Oの便宜的座標を有限点の反転公式へ代入してはならない。
補正和ではOの一項だけを別に数えると、余分な|H|a₃がちょうど消える。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open scoped BigOperators
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelReflection :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 反転で、平行移動した一般点は反対の移動量を持つ点の負になる。 -/
theorem map_neg_translated_generic (P : (E⁄(AlgebraicClosure K)).Point) :
    Point.map (negEquiv E (AlgebraicClosure K) : _ →ₐ[AlgebraicClosure K] _)
      (genericPoint E (AlgebraicClosure K) + Point.baseChange (AlgebraicClosure K) _ P) =
      -(genericPoint E (AlgebraicClosure K) + Point.baseChange (AlgebraicClosure K) _ (-P)) := by
  rw [map_add, map_negEquiv_genericPoint, Point.map_baseChange, map_neg, neg_add_rev, neg_neg]
  exact add_comm _ _

/-- [DkMath.Lib] 反転は平行移動xの移動量を負にする。一般点は常に有限点。 -/
theorem neg_translated_genericX_point (P : (E⁄(AlgebraicClosure K)).Point) :
    negEquiv E (AlgebraicClosure K) (transEquiv E (AlgebraicClosure K) P
      (genericX E (AlgebraicClosure K))) =
      transEquiv E (AlgebraicClosure K) (-P) (genericX E (AlgebraicClosure K)) := by
  rw [transEquiv_genericX, ← AlgEquiv.coe_toAlgHom, ← point_xc_map,
    map_neg_translated_generic]
  rw [Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero E (AlgebraicClosure K) (-P)),
    Point.neg_some, Point.xc_some, transEquiv_genericX]

/-- [DkMath.Lib] 平行移動yの反転公式。定数項a₃を落とさない。 -/
theorem neg_translated_genericY_point (P : (E⁄(AlgebraicClosure K)).Point) :
    negEquiv E (AlgebraicClosure K) (transEquiv E (AlgebraicClosure K) P
      (genericY E (AlgebraicClosure K))) =
      -transEquiv E (AlgebraicClosure K) (-P) (genericY E (AlgebraicClosure K)) -
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ *
        transEquiv E (AlgebraicClosure K) (-P) (genericX E (AlgebraicClosure K)) -
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ := by
  rw [transEquiv_genericY, ← AlgEquiv.coe_toAlgHom, ← point_yc_map,
    map_neg_translated_generic]
  rw [Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero E (AlgebraicClosure K) (-P)),
    Point.neg_some, Point.yc_some, negY, transEquiv_genericX, transEquiv_genericY]

/-- [DkMath.Lib] 同じ実点型Pointsの反転x公式。基礎の群構造を一致させる入口。 -/
theorem neg_translated_genericX (P : Points E) :
    negEquiv E (AlgebraicClosure K) (transEquiv E (AlgebraicClosure K) P
      (genericX E (AlgebraicClosure K))) =
      transEquiv E (AlgebraicClosure K) (-P) (genericX E (AlgebraicClosure K)) :=
  neg_translated_genericX_point E P

/-- [DkMath.Lib] 同じ実点型Pointsの反転y公式。 -/
theorem neg_translated_genericY (P : Points E) :
    negEquiv E (AlgebraicClosure K) (transEquiv E (AlgebraicClosure K) P
      (genericY E (AlgebraicClosure K))) =
      -transEquiv E (AlgebraicClosure K) (-P) (genericY E (AlgebraicClosure K)) -
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ *
        transEquiv E (AlgebraicClosure K) (-P) (genericX E (AlgebraicClosure K)) -
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ :=
  neg_translated_genericY_point E P

omit [E.IsElliptic] in
/-- [DkMath.Lib] 有限核の負写像は同じ和の添字を置換する。 -/
theorem sum_kernel_neg {M : Type*} [AddCommMonoid M]
    (H : AddSubgroup (Points E)) [Fintype H] (f : Points E → M) :
    (∑ P : H, f (-P.val)) = ∑ P : H, f P.val := by
  apply Fintype.sum_equiv (Equiv.neg H)
  intro P
  rfl

omit [E.IsElliptic] in
/-- [DkMath.Lib] 有限補正和の反転公式。Oの一項だけがa₃を残す。 -/
theorem kernel_coordinate_correction (H : AddSubgroup (Points E)) [Fintype H] :
    (∑ P : H, P.val.yc) + (∑ P : H, P.val.yc) +
      (E⁄(AlgebraicClosure K)).a₁ * (∑ P : H, P.val.xc) +
      (Fintype.card H : AlgebraicClosure K) * (E⁄(AlgebraicClosure K)).a₃ =
      (E⁄(AlgebraicClosure K)).a₃ := by
  have hpoint (P : Points E) (hP : P ≠ 0) :
      (-P).yc + P.yc + (E⁄(AlgebraicClosure K)).a₁ * P.xc +
        (E⁄(AlgebraicClosure K)).a₃ = 0 := by
    cases P with
    | zero => exact (hP rfl).elim
    | some x y h =>
      change (-y - (E⁄(AlgebraicClosure K)).a₁ * x - (E⁄(AlgebraicClosure K)).a₃) + y +
        (E⁄(AlgebraicClosure K)).a₁ * x + (E⁄(AlgebraicClosure K)).a₃ = 0
      ring
  have hs : (∑ P : H, ((-P.val).yc + P.val.yc +
      (E⁄(AlgebraicClosure K)).a₁ * P.val.xc + (E⁄(AlgebraicClosure K)).a₃)) =
      (E⁄(AlgebraicClosure K)).a₃ := by
    rw [Finset.sum_eq_single (0 : H)]
    · change (0 : AlgebraicClosure K) + 0 + _ * 0 + _ = _
      ring
    · intro P _ hP
      exact hpoint P.val (fun he => hP (Subtype.ext he))
    · simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  erw [sum_kernel_neg E H (fun P => P.yc)] at hs
  exact hs

/-- [DkMath.Lib] 同じ正規化x座標は反転で固定される。 -/
theorem negEquiv_veluX (H : AddSubgroup (Points E)) [Fintype H] :
    negEquiv E (AlgebraicClosure K) (veluX E H) = veluX E H := by
  rw [veluX, map_sub, AlgEquiv.commutes]
  congr 1
  simp only [kernelTrace, map_sum, neg_translated_genericX]
  exact sum_kernel_neg E H (fun P => transEquiv E (AlgebraicClosure K) P
    (genericX E (AlgebraicClosure K)))

/-- [DkMath.Lib] 同じ正規化y座標は元のa₁,a₃を持つWeierstrass反転に従う。
核の位数をa₃の係数として残してしまう誤りを、補正和のOの一項で除く。 -/
theorem negEquiv_veluY (H : AddSubgroup (Points E)) [Fintype H] :
    negEquiv E (AlgebraicClosure K) (veluY E H) =
      -veluY E H - (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ * veluX E H -
        (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ := by
  have hs := congrArg (algebraMap (AlgebraicClosure K)
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (kernel_coordinate_correction E H)
  simp only [map_add, map_mul, map_natCast] at hs
  rw [veluY, map_sub, AlgEquiv.commutes]
  simp only [kernelTrace, map_sum, neg_translated_genericY, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [sum_kernel_neg E H (fun P => transEquiv E (AlgebraicClosure K) P (genericY E (AlgebraicClosure K))),
    sum_kernel_neg E H (fun P => transEquiv E (AlgebraicClosure K) P (genericX E (AlgebraicClosure K)))]
  simp only [veluX, kernelTrace]
  have h₁ : algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      (E⁄(AlgebraicClosure K)).a₁ = (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ := by
    change algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₁) = algebraMap K _ E.a₁
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) _ _).symm
  have h₃ : algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      (E⁄(AlgebraicClosure K)).a₃ = (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ := by
    change algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₃) = algebraMap K _ E.a₃
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) _ _).symm
  rw [h₁, h₃] at hs
  simp only [map_sum] at hs ⊢
  linear_combination -hs

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
