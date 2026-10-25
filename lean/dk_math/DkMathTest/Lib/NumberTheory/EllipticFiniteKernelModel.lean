/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelModelDescent
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDegree

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelModel"

/-!
# 標的三次モデルの明と暗

明: y²=x³−xの同じ二元核で、方程式・単射・像・次数・ℚ係数への降下を検査する。
暗: 尖点曲線y²=x³には非特異な一般点(t²,t³)があり、二関数は全関数体を生成し、
次数も2,3であるが、原点は特異でΔ=0。これらの一般点情報だけから楕円性は出ない。
これは構成したkernelModelの反例ではなく、次の証明に必要な幾何学的入力の境界である。
-/
namespace EllipticFiniteKernelModelTest
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 同じ二元核の二関数は、実際に構成した同じモデルの方程式を満たす。 -/
theorem actual_equation :
    ((kernelModel curve kernel).toAffine⁄
      (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
        (veluX curve kernel) (veluY curve kernel) := kernelModel_equation curve kernel

/-- 座標環単射と非特異な一般点。標的全体の非特異性を仮定しない。 -/
theorem actual_generic_data :
    Function.Injective (kernelModelCoordinateHom curve kernel) ∧
    ((kernelModel curve kernel).toAffine⁄
      (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Nonsingular
        (veluX curve kernel) (veluY curve kernel) :=
  ⟨kernelModelCoordinateHom_injective curve kernel, kernelModel_generic_nonsingular curve kernel⟩

/-- 関数体の実際の単射・同じ固定体への像・次数2をまとめて確認する。 -/
theorem actual_pull_data :
    Function.Injective (kernelModelPull curve kernel) ∧
    (kernelModelPull curve kernel).fieldRange = kernelFixedField curve kernel ∧
    Module.finrank (kernelModelPull curve kernel).fieldRange
      (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 2 :=
  ⟨kernelModelPull_injective curve kernel, kernelModelPull_fieldRange curve kernel,
    (finrank_kernelModelPull curve kernel).trans degree_two.1⟩

/-- 個々の点を新しく選ばず、同じ二元核のモデルをℚへ降下する。 -/
theorem actual_rational_descent :
    ∃ W : WeierstrassCurve ℚ,
      W.map (algebraMap ℚ (AlgebraicClosure ℚ)) = kernelModel curve kernel ∧
      W.a₁ = curve.a₁ ∧ W.a₃ = curve.a₃ :=
  exists_descended_kernelModel curve kernel kernel_stable

/-- 自明核ではモデルが元の楕円曲線へ戻る。非特異性が確かに得られる明るい例。 -/
theorem trivial_model :
    letI : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
    kernelModel curve ⊥ = curve.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  let : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
  symm
  apply kernelModel_unique curve ⊥ _ rfl rfl
  rw [trivial_kernel.1, trivial_kernel.2]
  exact EllipticFunctionField.generic_equation curve (AlgebraicClosure ℚ)

/-- 自明核の同じモデルの判別式は64。一般点情報ではなくモデルの同一性から示す。 -/
theorem trivial_model_discriminant :
    letI : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
    (kernelModel curve ⊥).Δ = 64 := by
  let : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
  rw [trivial_model, WeierstrassCurve.map_Δ, curve_discriminant]
  norm_num

variable (k : Type*) [Field k]

/-- 対照用の尖点三次曲線。WeierstrassCurveは方程式の型であり、楕円性を含まない。 -/
def cusp : WeierstrassCurve k := ⟨0, 0, 0, 0, 0⟩

/-- 尖点曲線の判別式は零。 -/
theorem cusp_discriminant : (cusp k).Δ = 0 := by
  simp [cusp, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]

/-- 原点は方程式上の点だが、二つの偏微分がともに消える。 -/
theorem cusp_origin_singular :
    (cusp k).toAffine.Equation 0 0 ∧ ¬(cusp k).toAffine.Nonsingular 0 0 := by
  simp [equation_iff, nonsingular_iff', cusp]

/-- t²,t³は同じ尖点曲線の方程式を満たす。 -/
theorem cusp_equation :
    ((cusp k).toAffine⁄(RatFunc k)).Equation (RatFunc.X ^ 2) (RatFunc.X ^ 3) := by
  rw [equation_iff]
  simp only [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, cusp, map_zero, zero_mul, add_zero]
  ring

variable [CharZero k]

/-- 一般点は非特異。それでも原点の特異性と矛盾しない。 -/
theorem cusp_generic_nonsingular :
    ((cusp k).toAffine⁄(RatFunc k)).Nonsingular (RatFunc.X ^ 2) (RatFunc.X ^ 3) := by
  rw [nonsingular_iff']
  refine ⟨cusp_equation k, Or.inr ?_⟩
  simpa only [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, cusp, map_zero, zero_mul, add_zero] using
    mul_ne_zero (by norm_num : (2 : RatFunc k) ≠ 0) (pow_ne_zero 3 RatFunc.X_ne_zero)

omit [CharZero k] in
/-- 尖点の場合でも、二座標の次数2,3と全関数体の生成が同時に成立する。 -/
theorem cusp_degrees_and_generation :
    Module.finrank k⟮(RatFunc.X : RatFunc k) ^ 2⟯ (RatFunc k) = 2 ∧
    Module.finrank k⟮(RatFunc.X : RatFunc k) ^ 3⟯ (RatFunc k) = 3 ∧
    adjoin k {(RatFunc.X : RatFunc k) ^ 2, RatFunc.X ^ 3} = ⊤ := by
  refine ⟨EllipticFiniteKernelDegreeTest.powerField_degree k 2,
    EllipticFiniteKernelDegreeTest.powerField_degree k 3, ?_⟩
  rw [← Set.singleton_union, adjoin_union]
  exact EllipticFiniteKernelDegreeTest.coprime_two_three k

/-- 方程式・非特異な一般点・次数2,3・生成が揃っても、Δ≠0を結論してはいけない。 -/
theorem cusp_boundary :
    ((cusp k).toAffine⁄(RatFunc k)).Nonsingular (RatFunc.X ^ 2) (RatFunc.X ^ 3) ∧
    adjoin k {(RatFunc.X : RatFunc k) ^ 2, RatFunc.X ^ 3} = ⊤ ∧
    (cusp k).Δ = 0 ∧ ¬(cusp k).toAffine.Nonsingular 0 0 :=
  ⟨cusp_generic_nonsingular k, (cusp_degrees_and_generation k).2.2,
    cusp_discriminant k, (cusp_origin_singular k).2⟩

end
end EllipticFiniteKernelModelTest
