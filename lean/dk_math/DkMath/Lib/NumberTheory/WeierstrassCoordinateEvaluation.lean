/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Coordinate evaluation is adapted from DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom,
originally Definitions/Def_EllipticCurve_FunctionFieldPullback.lean,
blob ce8783a9e9613db1c4c0323ce93fb0d89917ee65.
Modified: arbitrary target field, equation input, no IsElliptic assumption;
injectivity from actual transcendence and quadratic nonmembership.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldGenerators
import DkMath.Lib.NumberTheory.EllipticFunctionField

#print "file: DkMath.Lib.NumberTheory.WeierstrassCoordinateEvaluation"

/-!
# 方程式の実現から座標環と分数体の単射へ

[DkMath.Lib] Weierstrass方程式を満たすx,yへの代入を、任意の係数拡大体Fへ構成する。
xが超越的でy∉k(x)なら二元基底p(x)+q(x)yから代入の単射性が従う。
標的曲線の判別式や楕円性を入力にせず、特異モデルも扱う。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassCoordinateEvaluation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
open scoped Polynomial.Bivariate
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (W : WeierstrassCurve k) (x y : F)

/-- [DkMath.Lib] 任意の拡大体の方程式解は、座標環を定義する二変数多項式を消す。 -/
theorem equation_eval₂ (h : (W.toAffine⁄F).Equation x y) :
    W.toAffine.polynomial.eval₂ (aeval (R := k) x).toRingHom y = 0 := by
  have he := (equation_iff _ _).mp h
  change y ^ 2 + algebraMap k F W.toAffine.a₁ * x * y + algebraMap k F W.toAffine.a₃ * y =
    x ^ 3 + algebraMap k F W.toAffine.a₂ * x ^ 2 + algebraMap k F W.toAffine.a₄ * x +
      algebraMap k F W.toAffine.a₆ at he
  simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_add, map_mul, map_pow, aeval_C, aeval_X]
  linear_combination he

/-- [DkMath.Lib] 任意の拡大体の方程式解への、実際の座標環代入。 -/
noncomputable def coordinateEval (h : (W.toAffine⁄F).Equation x y) :
    W.toAffine.CoordinateRing →ₐ[k] F :=
  { AdjoinRoot.lift (aeval (R := k) x).toRingHom y (equation_eval₂ W x y h) with
    commutes' := fun c => by
      change AdjoinRoot.lift (aeval x).toRingHom y (equation_eval₂ W x y h)
        (algebraMap k W.toAffine.CoordinateRing c) = algebraMap k F c
      rw [IsScalarTower.algebraMap_apply k k[X] W.toAffine.CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Polynomial.algebraMap_apply, aeval_C]
      rfl }

/-- [DkMath.Lib] 二変数多項式類への代入は、二段の実際の多項式評価である。 -/
theorem coordinateEval_mk (h : (W.toAffine⁄F).Equation x y) (p : k[X][X]) :
    coordinateEval W x y h (CoordinateRing.mk W.toAffine p) = p.eval₂ (aeval x).toRingHom y :=
  AdjoinRoot.lift_mk (equation_eval₂ W x y h) p

/-- [DkMath.Lib] xだけの多項式の代入公式。 -/
theorem coordinateEval_mk_C (h : (W.toAffine⁄F).Equation x y) (p : k[X]) :
    coordinateEval W x y h (CoordinateRing.mk W.toAffine (C p)) = aeval x p := by
  rw [coordinateEval_mk, eval₂_C]
  rfl

/-- [DkMath.Lib] y座標そのものの代入公式。 -/
theorem coordinateEval_mk_Y (h : (W.toAffine⁄F).Equation x y) :
    coordinateEval W x y h (CoordinateRing.mk W.toAffine Y) = y := by
  rw [coordinateEval_mk, eval₂_X]

/-- [DkMath.Lib] 同じ二元基底の任意の座標環元を、p(x)+q(x)yへ送る。 -/
theorem coordinateEval_basis (h : (W.toAffine⁄F).Equation x y) (p q : k[X]) :
    coordinateEval W x y h (p • (1 : W.toAffine.CoordinateRing) + q • CoordinateRing.mk W.toAffine Y) =
      aeval x p + aeval x q * y := by
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul,
    coordinateEval_mk_C, coordinateEval_mk_C, coordinateEval_mk_Y]

/-- [DkMath.Lib] xの超越性とy∉k(x)は、方程式代入の核が零であることを保証する。
一般点での非特異性や曲線全体の楕円性を仮定しない。 -/
theorem coordinateEval_injective (h : (W.toAffine⁄F).Equation x y)
    (hx : Transcendental k x) (hy : y ∉ k⟮x⟯) : Function.Injective (coordinateEval W x y h) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [coordinateEval_basis] at ha
  have hq : q = 0 := by
    by_contra hq
    have hqx : aeval x q ≠ 0 := fun h => hq ((transcendental_iff.mp hx) q h)
    have he : y = -aeval x p / aeval x q := by
      apply (eq_div_iff hqx).mpr
      linear_combination ha
    apply hy
    rw [he]
    have hpoly (r : k[X]) : aeval x r ∈ k⟮x⟯ :=
      (algebra_adjoin_le_adjoin k {x}) (Polynomial.aeval_mem_adjoin_singleton k x)
    exact div_mem (neg_mem (hpoly p)) (hpoly q)
  rw [hq, map_zero, zero_mul, add_zero] at ha
  have hp : p = 0 := (transcendental_iff.mp hx) p ha
  simp [hp, hq]

/-- [DkMath.Lib] 単射な座標代入を、同じモデルの実際の分数体からの代数準同型へ延長する。 -/
noncomputable def functionPull (h : (W.toAffine⁄F).Equation x y)
    (hx : Transcendental k x) (hy : y ∉ k⟮x⟯) : W.toAffine.FunctionField →ₐ[k] F :=
  IsFractionRing.liftAlgHom (coordinateEval_injective W x y h hx hy)

/-- [DkMath.Lib] 分数体への延長は座標環上の同じ代入に一致する。 -/
theorem functionPull_algebraMap (h : (W.toAffine⁄F).Equation x y)
    (hx : Transcendental k x) (hy : y ∉ k⟮x⟯) (a : W.toAffine.CoordinateRing) :
    functionPull W x y h hx hy (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a) =
      coordinateEval W x y h a := by
  rw [functionPull, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- [DkMath.Lib] 引き戻しの像は同じ二座標が生成する実際の部分体に等しい。 -/
theorem functionPull_fieldRange (h : (W.toAffine⁄F).Equation x y)
    (hx : Transcendental k x) (hy : y ∉ k⟮x⟯) :
    (functionPull W x y h hx hy).fieldRange = adjoin k {x, y} := by
  let φ := functionPull W x y h hx hy
  have ht : (⊤ : IntermediateField k W.toAffine.FunctionField).map φ = φ.fieldRange := by
    ext z
    simp
  rw [← ht, ← EllipticFunctionField.functionField_adjoin_X_Y W,
    adjoin_map, Set.image_pair]
  dsimp only [φ]
  rw [functionPull_algebraMap, coordinateEval_mk_C, aeval_X,
    functionPull_algebraMap, coordinateEval_mk_Y]

/-- [DkMath.Lib] 同じ超越xと同じyの方程式で、a₁,a₃を固定すれば残り三係数も一意。
モデルの変数変換による同型ではなく、同じ座標での実際の係数の等式である。 -/
theorem eq_of_same_equation (V : WeierstrassCurve k) (hx : Transcendental k x)
    (h₁ : W.a₁ = V.a₁) (h₃ : W.a₃ = V.a₃)
    (hW : (W.toAffine⁄F).Equation x y) (hV : (V.toAffine⁄F).Equation x y) : W = V := by
  have hw := (equation_iff _ _).mp hW
  have hv := (equation_iff _ _).mp hV
  change y ^ 2 + algebraMap k F W.a₁ * x * y + algebraMap k F W.a₃ * y =
    x ^ 3 + algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆ at hw
  change y ^ 2 + algebraMap k F V.a₁ * x * y + algebraMap k F V.a₃ * y =
    x ^ 3 + algebraMap k F V.a₂ * x ^ 2 + algebraMap k F V.a₄ * x + algebraMap k F V.a₆ at hv
  rw [h₁, h₃] at hw
  have he : aeval x (C (W.a₂ - V.a₂) * X ^ 2 + C (W.a₄ - V.a₄) * X + C (W.a₆ - V.a₆)) = 0 := by
    simp only [map_add, map_mul, map_sub, aeval_C, map_pow, aeval_X]
    linear_combination hv - hw
  have hp := (transcendental_iff.mp hx) _ he
  have h₂ : W.a₂ = V.a₂ := sub_eq_zero.mp (by
    simpa [coeff_mul_X_pow'] using congrArg (fun p : k[X] => p.coeff 2) hp)
  have h₄ : W.a₄ = V.a₄ := sub_eq_zero.mp (by
    simpa [coeff_mul_X_pow'] using congrArg (fun p : k[X] => p.coeff 1) hp)
  have h₆ : W.a₆ = V.a₆ := sub_eq_zero.mp (by
    simpa [coeff_mul_X_pow'] using congrArg (fun p : k[X] => p.coeff 0) hp)
  cases W
  cases V
  simp_all only

end DkMath.Lib.NumberTheory.WeierstrassCoordinateEvaluation
