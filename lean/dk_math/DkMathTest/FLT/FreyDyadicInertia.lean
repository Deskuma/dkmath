/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDyadicInertia
import Mathlib.LinearAlgebra.Dimension.Constructions

#print "file: DkMathTest.FLT.FreyDyadicInertia"

/-!
# NOTE-031-003の回帰例

F₃²上の非恒等な上三角単冪作用でも、共役二乗関係から同じ直線と商は固定される。
全空間の固定へ結論を強めていないことを、この非恒等例で確認する。
指数37の例は任意のSourceを入力として保ち、整数反例の存在を主張しない。
-/
namespace FreyDyadicInertiaTest
open DkMath.Lib.RepresentationTheory DkMath.Lib.NumberTheory

/-- y座標をxへ加える単冪作用。全空間の恒等ではない。 -/
def shear : (ZMod 3 × ZMod 3) →ₗ[ZMod 3] (ZMod 3 × ZMod 3) where
  toFun v := (v.1 + v.2, v.2)
  map_add' _ _ := by ext <;> dsimp; ring
  map_smul' _ _ := by ext <;> dsimp; ring

/-- x座標のみを2倍する共役作用。F₃上では自身が逆作用でもある。 -/
def diagonal : (ZMod 3 × ZMod 3) →ₗ[ZMod 3] (ZMod 3 × ZMod 3) where
  toFun v := (2 * v.1, v.2)
  map_add' _ _ := by ext <;> dsimp; ring
  map_smul' _ _ := by ext <;> dsimp; ring

/-- 同じ水平直線を部分加群として保持する。 -/
def line : Submodule (ZMod 3) (ZMod 3 × ZMod 3) :=
  LinearMap.ker (LinearMap.snd (ZMod 3) (ZMod 3) (ZMod 3))

/-- 非恒等作用の例でも、直線と商の固定が同時に従う。 -/
theorem shear_fixed_cofixed :
    (∀ x ∈ line, shear x = x) ∧ (∀ x, shear x - x ∈ line) := by
  have hb : line ≠ ⊥ := by
    intro h
    have hm : ((1, 0) : ZMod 3 × ZMod 3) ∈ line := by simp [line]
    rw [h, Submodule.mem_bot] at hm
    exact one_ne_zero (congrArg Prod.fst hm)
  have ht : line ≠ ⊤ := by
    intro h
    have hm : ((0, 1) : ZMod 3 × ZMod 3) ∈ line := by rw [h]; trivial
    simp [line] at hm
  apply ConjugateSquare.eq_id_on_line_of_conj_eq_sq (by simp) line hb ht shear diagonal diagonal
  · intro x y h
    have hy := congrArg Prod.snd h
    have hx := congrArg Prod.fst h
    dsimp [shear] at hx hy
    exact Prod.ext (add_right_cancel (hx.trans (congrArg (fun t => y.1 + t) hy.symm))) hy
  · intro x
    ext <;> dsimp [diagonal]
    · have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      rw [← mul_assoc, h4, one_mul]
  · intro x hx
    simpa [line, shear] using hx
  · intro x hx
    simpa [line, diagonal] using hx
  · intro x hx
    simpa [line, diagonal] using hx
  · intro x
    ext <;> dsimp [diagonal, shear]
    · have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      calc 2 * (2 * x.1 + x.2) = (2 * 2) * x.1 + (x.2 + x.2) := by ring
        _ = x.1 + x.2 + x.2 := by rw [h4]; ring

/-- 上の例の作用は全空間では恒等でない。 -/
theorem shear_not_identity : shear ((0, 1) : ZMod 3 × ZMod 3) ≠ (0, 1) := by
  intro h
  have := congrArg Prod.fst h
  norm_num [shear] at this

/-- 非正則素数37でも、この2上の局所定理は同じSourceと安定直線へ適用できる。
正則素数性・大域二択・野生固定のproviderは追加しない。 -/
theorem source37_fixed_cofixed (S : DkMath.FLT.Frey.Source 37)
    (N : Submodule (ZMod 37) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A 2) :
    LocalFixedCofixed.FixedOn S.residualRepresentation N (ValuationInertia.inertiaSubgroupIn A ℚ) ∧
      LocalFixedCofixed.CofixedOn S.residualRepresentation N (ValuationInertia.inertiaSubgroupIn A ℚ) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact S.residual_fixed_and_cofixed_at_two (by decide) N hN hbot htop A hA

end FreyDyadicInertiaTest
