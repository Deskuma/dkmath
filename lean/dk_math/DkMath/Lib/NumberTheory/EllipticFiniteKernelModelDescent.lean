/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelModelMap
import DkMath.Lib.NumberTheory.EllipticFiniteKernelGalois
import DkMath.Lib.NumberTheory.EllipticFixedTorsion

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelModelDescent"

/-!
# 同じ核がガロア安定なら、同じ三次モデルの係数は元の体へ降りる

[DkMath.Lib] 関数のガロア不変性だけで止めず、同じ方程式の係数の一意性を使う。
係数ごとの固定体定理で実際のK係数Weierstrassモデルを構成する。
この降下は三次方程式の降下であり、Δ≠0や有理isogenyを仮定に隠さない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
variable {K : Type*} [Field K] [NeZero (2 : K)] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelModelDescent :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じ二関数の不変性と係数の一意性により、モデル自身もガロア固定となる。 -/
theorem kernelModel_galois (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (σ : Field.absoluteGaloisGroup K) :
    (kernelModel E H).map σ.toRingHom = kernelModel E H := by
  apply kernelModel_unique E H
  · rw [WeierstrassCurve.map_a₁, kernelModel_a₁]
    exact σ.commutes E.a₁
  · rw [WeierstrassCurve.map_a₃, kernelModel_a₃]
    exact σ.commutes E.a₃
  · have he := (equation_iff _ _).mp (kernelModel_equation E H)
    change veluY E H ^ 2 + algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₁ *
      veluX E H * veluY E H + algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₃ * veluY E H =
      veluX E H ^ 3 + algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₂ * veluX E H ^ 2 +
      algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₄ * veluX E H +
      algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₆ at he
    have hg := congrArg (galFunctionFieldEquiv E σ) he
    have hconst (c : AlgebraicClosure K) : galFunctionFieldEquiv E σ
        (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) =
        algebraMap (AlgebraicClosure K) _ (σ.toAlgHom c) := gal_algebraMap E σ c
    rw [equation_iff]
    change veluY E H ^ 2 + algebraMap (AlgebraicClosure K) _ (σ.toAlgHom (kernelModel E H).a₁) *
      veluX E H * veluY E H + algebraMap (AlgebraicClosure K) _ (σ.toAlgHom (kernelModel E H).a₃) *
      veluY E H = veluX E H ^ 3 + algebraMap (AlgebraicClosure K) _ (σ.toAlgHom (kernelModel E H).a₂) *
      veluX E H ^ 2 + algebraMap (AlgebraicClosure K) _ (σ.toAlgHom (kernelModel E H).a₄) *
      veluX E H + algebraMap (AlgebraicClosure K) _ (σ.toAlgHom (kernelModel E H).a₆)
    simpa only [map_add, map_mul, map_pow, hconst,
      veluX_galois E H hH, veluY_galois E H hH] using hg

variable [CharZero K]

/-- [DkMath.Lib] 同じ安定核から得たモデルの三つの新係数を元の体Kへ降下する。
存在するのは同じモデルのK係数表示であり、楕円性や点写像の存在ではない。 -/
theorem exists_descended_kernelModel (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    ∃ W : WeierstrassCurve K, W.map (algebraMap K (AlgebraicClosure K)) = kernelModel E H ∧
      W.a₁ = E.a₁ ∧ W.a₃ = E.a₃ := by
  have h₂ : ∀ σ : Field.absoluteGaloisGroup K, σ.toAlgHom (kernelModel E H).a₂ = (kernelModel E H).a₂ :=
    fun σ => congrArg WeierstrassCurve.a₂ (kernelModel_galois E H hH σ)
  have h₄ : ∀ σ : Field.absoluteGaloisGroup K, σ.toAlgHom (kernelModel E H).a₄ = (kernelModel E H).a₄ :=
    fun σ => congrArg WeierstrassCurve.a₄ (kernelModel_galois E H hH σ)
  have h₆ : ∀ σ : Field.absoluteGaloisGroup K, σ.toAlgHom (kernelModel E H).a₆ = (kernelModel E H).a₆ :=
    fun σ => congrArg WeierstrassCurve.a₆ (kernelModel_galois E H hH σ)
  obtain ⟨a₂, ha₂⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr h₂
  obtain ⟨a₄, ha₄⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr h₄
  obtain ⟨a₆, ha₆⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr h₆
  refine ⟨⟨E.a₁, a₂, E.a₃, a₄, a₆⟩, ?_, rfl, rfl⟩
  have h₁ := kernelModel_a₁ E H
  have h₃ := kernelModel_a₃ E H
  cases hmodel : kernelModel E H
  simp only [hmodel] at ha₂ ha₄ ha₆ h₁ h₃
  simp_all only [WeierstrassCurve.map, WeierstrassCurve.mk.injEq]
  exact ⟨rfl, True.intro, rfl, True.intro, True.intro⟩

/-- [DkMath.Lib] 同じ安定核のK係数三次モデル。IsEllipticのインスタンスはまだ持たない。 -/
noncomputable def descendedKernelModel (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) : WeierstrassCurve K :=
  Classical.choose (exists_descended_kernelModel E H hH)

/-- [DkMath.Lib] 選んだK係数モデルの基底変換は、同じ代数閉包モデルと実際に一致する。 -/
theorem descendedKernelModel_map (H : AddSubgroup (Points E)) [Fintype H]
    (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    (descendedKernelModel E H hH).map (algebraMap K (AlgebraicClosure K)) = kernelModel E H :=
  (Classical.choose_spec (exists_descended_kernelModel E H hH)).1

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
