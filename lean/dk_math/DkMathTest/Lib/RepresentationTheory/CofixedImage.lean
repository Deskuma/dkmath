/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticCofixedImage
import DkMathTest.Lib.RepresentationTheory.CofixedDeterminant

#print "file: DkMathTest.Lib.RepresentationTheory.CofixedImage"

/-!
005C₁の境界。射影の同じ像と商を比較し、零写像・同変性・Cofixed性の各条件を調べる。
楕円曲線の実際の[p]倍写像も検査し、p捩れを全て消す写像を直線核と取り違えない。
-/
namespace CofixedImageTest
open Module DkMath.Lib.RepresentationTheory CofixedDeterminantTest
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

/-- 単元が通常のスカラー倍で作用する表現。 -/
def unitScalar : Representation ℚ ℚˣ ℚ where
  toFun u := (u : ℚ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' := by intro u v; ext; simp [smul_smul, mul_comm]

/-- 同じ第二射影の像は非零で固定され、商の代表元はその第二座標へ写る。 -/
theorem projection_positive :
    (∀ u, Representation.trivial ℚ ℚˣ ℚ u
      ((LinearMap.snd ℚ ℚ ℚ) (0, 1)) = (1 : ℚ)) ∧
    finrank ℚ (LinearMap.range (LinearMap.snd ℚ ℚ ℚ)) = 1 ∧
    (CofixedImage.quotientEquivRange (LinearMap.snd ℚ ℚ ℚ) axis rfl
      (axis.mkQ (0, 1))).val = (1 : ℚ) := by
  refine ⟨?_, CofixedImage.finrank_range _ axis (by simp) axis_finrank rfl, ?_⟩
  · intro u
    exact CofixedImage.image_fixed unitShear (Representation.trivial ℚ ℚˣ ℚ)
      (LinearMap.snd ℚ ℚ ℚ) axis unitShear_cofixed le_rfl (fun _ _ => rfl) (0, 1) u
  · exact CofixedImage.quotientEquivRange_apply_val _ axis rfl (0, 1)

/-- 核の包含だけなら零写像が通る。非零の像を取り出す段階では核の一致が必要。 -/
theorem zero_map_boundary :
    axis ≤ LinearMap.ker (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ) ∧
    LinearMap.ker (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ) ≠ axis ∧
    ¬ ∃ x : ℚ × ℚ, (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ) x ≠ 0 := by
  refine ⟨by simp, ?_, by simp⟩
  intro h
  have hm : ((0, 1) : ℚ × ℚ) ∈ LinearMap.ker (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ) := by simp
  rw [h] at hm
  exact one_ne_zero hm

/-- 同じCofixed核を持っていても、標的の作用を変えると同変性と像の固定性は失われる。 -/
theorem equivariance_boundary :
    IsCofixedOn unitShear axis ∧
    LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) = axis ∧
    (let u : ℚˣ := Units.mk0 2 (by norm_num);
      (LinearMap.snd ℚ ℚ ℚ) (unitShear u (0, 1)) ≠
        unitScalar u ((LinearMap.snd ℚ ℚ ℚ) (0, 1))) := by
  refine ⟨unitShear_cofixed, rfl, ?_⟩
  norm_num [unitShear, unitScalar]

/-- 同変写像の核が安定でも、像が固定されるとは限らない。
同じ単元のスカラー作用を定義域へ戻すとCofixed性が失われる。 -/
theorem cofixed_boundary :
    (∀ (u : ℚˣ) (x : ℚ × ℚ), (u : ℚ) • x ∈ axis ↔ x ∈ axis) ∧
    (∀ (u : ℚˣ) (x : ℚ × ℚ), (LinearMap.snd ℚ ℚ ℚ) ((u : ℚ) • x) =
      unitScalar u ((LinearMap.snd ℚ ℚ ℚ) x)) ∧
    (let u : ℚˣ := Units.mk0 2 (by norm_num);
      ((u : ℚ) • ((0, 1) : ℚ × ℚ) - (0, 1)) ∉ axis ∧ unitScalar u 1 ≠ 1) := by
  refine ⟨?_, fun _ _ => rfl, ?_⟩
  · intro u x
    change (u : ℚ) * x.2 = 0 ↔ x.2 = 0
    exact mul_eq_zero.trans (or_iff_right (Units.ne_zero u))
  · norm_num [axis, unitScalar]

/-- 実際の[p]倍写像はE[p]全体を消す。核が一次元という仮定には適合しない。
この反例は抽象ベクトル空間ではなく、同じ曲線の実点上で検査する。 -/
theorem multiplication_kernel_boundary {K : Type*} [Field K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic] (p : ℕ) [Fact p.Prime] :
    torsionPointMap E E p (nsmulAddMonoidHom p) = 0 ∧
    ∀ L : Submodule (ZMod p) (Torsion E p), finrank (ZMod p) L = 1 →
      (nsmulAddMonoidHom p : Points E →+ Points E).ker ≠ pointSubgroup E p L := by
  have hz : torsionPointMap E E p (nsmulAddMonoidHom p) = 0 := by
    ext P
    exact P.property
  refine ⟨hz, ?_⟩
  intro L hline hker
  have hk := torsionPointMap_ker E E p (nsmulAddMonoidHom p) L hker
  rw [hz, LinearMap.ker_zero] at hk
  have htop : L = ⊤ := hk.symm
  rw [htop, finrank_top, finrank_torsion_prime E p] at hline
  omega

end CofixedImageTest
