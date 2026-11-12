/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLine
import DkMathTest.FLT.FreyResidualGL2

#print "file: DkMathTest.FLT.FreyStableLine"

/-!
# NOTE-029: 実際の点・指数の境界と、行列式だけでは足りないことの回帰

Source 2の既存の実在例で、抽出した部分群の位数2・固定点の降下を確認する。
同じ実在曲線の37-torsionでも一般の位数公式を検査するので、Source 37の反例の
存在には依存しない。後半の有限群表現は算術的Frey表現とは別の境界反例である。
-/

namespace FreyStableLineTest
open Module DkMath.FLT.Frey
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open FreyResidualRepresentationTest FreyResidualGL2Test

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- 実在する可約なSource 2から、元の点群の位数2の安定巡回部分群が得られる。 -/
theorem actual_two_subgroup :
    ∃ L : Submodule (ZMod 2) sample.ResidualSpace, finrank (ZMod 2) L = 1 ∧
      sample.IsGaloisStable L ∧ Nat.card (pointSubgroup sample.rationalCurve 2 L) = 2 ∧
      IsAddCyclic (pointSubgroup sample.rationalCurve 2 L) ∧
      (∀ P ∈ pointSubgroup sample.rationalCurve 2 L, 2 • P = 0) ∧
      (∀ σ P, P ∈ pointSubgroup sample.rationalCurve 2 L →
        pointAction sample.rationalCurve σ P ∈ pointSubgroup sample.rationalCurve 2 L) :=
  sample.residual_exists_stable_pointSubgroup actual2_rank_two_reducible.2

/-- 位数37の結論は、実在曲線の任意の一次元37-torsion部分空間で成立する。 -/
theorem actual_thirtySeven_card
    (L : Submodule (ZMod 37) (Torsion sample.rationalCurve 37)) (hL : finrank (ZMod 37) L = 1) :
    Nat.card (pointSubgroup sample.rationalCurve 37 L) = 37 :=
  card_pointSubgroup sample.rationalCurve 37 L hL

/-- 実際の非零固定2-torsion点が、非零有理2-torsion点へ降下する。 -/
theorem actual_two_descends :
    ∃ Q : sample.rationalCurve.toAffine.Point, Q ≠ 0 ∧ 2 • Q = 0 ∧
      baseChangePoint sample.rationalCurve Q = twoPoint.val := by
  obtain ⟨Q, hQ, heq⟩ := exists_rational_torsion_of_fixed sample.rationalCurve 2 twoPoint twoPoint_fixed
  refine ⟨Q, ?_, hQ, heq⟩
  intro hz
  apply twoPoint_ne_zero
  apply Subtype.ext
  rw [← heq, hz]
  rfl

/-- p=2では有理torsion排除は偽。一般のSourceにp≥5の算術を混入できない。 -/
theorem actual_two_has_fixed : ¬ NoNonzeroFixed sample.residualRepresentation := by
  intro h
  exact twoPoint_ne_zero (h twoPoint twoPoint_fixed)

/-- 一般の降下同値は37でも有効で、有理torsion排除を結論として先取りしない。 -/
theorem actual_thirtySeven_fixed_iff :
    NoNonzeroFixed (representation sample.rationalCurve 37) ↔
      ∀ Q : sample.rationalCurve.toAffine.Point, 37 • Q = 0 → Q = 0 :=
  noNonzeroFixed_iff_rational_torsion sample.rationalCurve 37

/-- 37で付値軌道の法の約分を検査する。vは任意の整数のまま。 -/
theorem cancel_thirtySeven (v m : ℤ) (h : 2 * (37 * v - 4) ∣ 37 * m) :
    2 * (37 * v - 4) ∣ m :=
  FoldedValuationOrbit.cancel_prime_modulus 37 (by decide) (by decide) v m h

/-- 奇素数条件を外せない。p=2,v=3では法4が2mを割ってもmを割らない。 -/
theorem cancellation_fails_at_two :
    (4 : ℤ) ∣ 2 * 2 ∧ ¬ (4 : ℤ) ∣ 2 := by decide

namespace DeterminantBoundary
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev k := ZMod 5
abbrev V := Fin 2 → k
abbrev G := kˣ

/-- 二つの非自明な指標g²とg³を対角成分に持つ作用素。 -/
def action (g : G) : V →ₗ[k] V where
  toFun x i := (g : k) ^ (if i = 0 then 2 else 3) * x i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' a x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- 有限群F₅ˣの実際の二次元表現。Frey表現や絶対ガロア表現の代用ではない。 -/
def rho : Representation k G V where
  toFun := action
  map_one' := by ext x i; simp [action]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    funext i
    by_cases hi : i = 0 <;> simp [action, hi, mul_pow, mul_assoc]

/-- 第一座標の軸。 -/
def line : Submodule k V := LinearMap.ker (LinearMap.proj (1 : Fin 2))

/-- 第一軸は、非零な第一単位ベクトルが生成する直線である。 -/
theorem line_eq_span : line = Submodule.span k ({![1, 0]} : Set V) := by
  ext x
  constructor
  · intro hx
    change x 1 = 0 at hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i <;> simp [hx]
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change (a • (![1, 0] : V)) 1 = 0
    simp

/-- 境界反例の部分空間は実際に一次元であり、零や全体を使った反例ではない。 -/
theorem line_finrank : finrank k line = 1 := by
  rw [line_eq_span]
  apply finrank_span_singleton (K := k) (v := (![1, 0] : V))
  intro h
  have he := congrFun h 0
  exact (by decide : (1 : k) ≠ 0) he

/-- 第一軸は安定である。 -/
theorem line_stable : IsStable rho line := by
  intro g x hx
  change (g : k) ^ 3 * x 1 = 0
  change x 1 = 0 at hx
  rw [hx, mul_zero]

/-- 行列式はg自身となり、指標は全射である。それでもfixed/cofixed二択は出ない。 -/
theorem determinant (g : G) : LinearMap.det (rho g) = (g : k) := by
  have ha : action g = Matrix.toLin' (Matrix.diagonal
      (fun i : Fin 2 => (g : k) ^ (if i = 0 then 2 else 3))) := by
    apply LinearMap.ext
    intro x
    funext i
    simp [action, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  change LinearMap.det (action g) = _
  rw [ha, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  exact (by decide : ∀ g : G, (g : k) ^ 2 * (g : k) ^ 3 = (g : k)) g

/-- g=2の第一対角成分は4なので、第一軸は点ごとには固定されない。 -/
theorem line_not_fixed : ¬ IsFixedOn rho line := by
  let g : G := ⟨2, 3, by decide, by decide⟩
  let x : V := ![1, 0]
  intro h
  have hx : x ∈ line := by change x 1 = 0; rfl
  have he := congrFun (h g x hx) 0
  change (2 : k) ^ 2 * 1 = 1 at he
  exact (by decide : (2 : k) ^ 2 * 1 ≠ 1) he

/-- g=2の商上の成分は3なので、第一軸で割った商も固定されない。 -/
theorem line_not_cofixed : ¬ IsCofixedOn rho line := by
  let g : G := ⟨2, 3, by decide, by decide⟩
  let x : V := ![0, 1]
  intro h
  have he := h g x
  change (2 : k) ^ 3 * 1 - 1 = 0 at he
  exact (by decide : (2 : k) ^ 3 * 1 - 1 ≠ 0) he

/-- 非自明な全射行列式を持っても、安定部分空間の二択には別の入力が必要である。 -/
theorem stable_without_dichotomy : IsStable rho line ∧
    ¬ (IsFixedOn rho line ∨ IsCofixedOn rho line) :=
  ⟨line_stable, fun h => h.elim line_not_fixed line_not_cofixed⟩

end DeterminantBoundary
end FreyStableLineTest
