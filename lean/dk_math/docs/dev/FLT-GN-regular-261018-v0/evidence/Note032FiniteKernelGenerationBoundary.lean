import DkMath.Lib.NumberTheory.EllipticFiniteKernelGeneration
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernel

#print "file: Note032FiniteKernelGenerationBoundary"

/-!
同じ曲線y²=x³−x、同じ実核H={O,(1,0)}で、前回仮定だった次数と生成を無条件に検査する。
自明核も含め、位数が奇数や素数という条件をLib側へ紛れ込ませない。
-/
namespace EllipticFiniteKernelGenerationTest
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open EllipticFiniteKernelTest
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 同じ実核の相対次数2,3を仮定なしで計算する。 -/
theorem actual_relative_degrees :
    ((AlgebraicClosure ℚ)⟮veluX curve kernel⟯).relfinrank (kernelFixedField curve kernel) = 2 ∧
    ((AlgebraicClosure ℚ)⟮veluY curve kernel⟯).relfinrank (kernelFixedField curve kernel) = 3 :=
  velu_relative_degrees curve kernel

/-- 同じ二元核で周囲の次数は4,6。核の位数2と相対次数を区別する。 -/
theorem actual_ambient_degrees :
    Module.finrank (AlgebraicClosure ℚ)⟮veluX curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 4 ∧
    Module.finrank (AlgebraicClosure ℚ)⟮veluY curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 6 := by
  have hc : Nat.card kernel = 2 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, kernel_univ]
    have hn : (0 : kernel) ≠ ⟨Q, Or.inr rfl⟩ := by
      intro he
      exact point_data.1 (congrArg Subtype.val he).symm
    simp [hn]
  simpa only [hc] using velu_ambient_degrees curve kernel

/-- 同じ二関数が同じ平行移動固定体を生成する。次数の外部仮定はない。 -/
theorem actual_generation : veluCoordinateField curve kernel = kernelFixedField curve kernel :=
  veluCoordinateField_eq_fixedField curve kernel

/-- 同じY_Hの実際の最小多項式は正確に二次である。 -/
theorem actual_minpoly_degree :
    (minpoly (AlgebraicClosure ℚ)⟮veluX curve kernel⟯ (veluY curve kernel)).natDegree = 2 :=
  natDegree_minpoly_veluY curve kernel

/-- 同じ二関数のモニック二次関係を実際の多項式として得る。 -/
theorem actual_quadratic :
    ∃ q : ((AlgebraicClosure ℚ)⟮veluX curve kernel⟯)[X],
      q.Monic ∧ q.natDegree = 2 ∧ aeval (veluY curve kernel) q = 0 :=
  exists_velu_quadratic_relation curve kernel

/-- 自明核の極位数2,3も同じ一般定理で計算できる。 -/
theorem trivial_kernel_degrees :
    Module.finrank (AlgebraicClosure ℚ)⟮veluX curve ⊥⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 2 ∧
    Module.finrank (AlgebraicClosure ℚ)⟮veluY curve ⊥⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 3 := by
  simpa using velu_ambient_degrees curve (⊥ : AddSubgroup (Points curve))

/-- 自明核でも、同じ生成体の等式を得る。二関数の独立性や核の非自明性を要求しない。 -/
theorem trivial_kernel_generation : veluCoordinateField curve ⊥ = kernelFixedField curve ⊥ :=
  veluCoordinateField_eq_fixedField curve ⊥

end
end EllipticFiniteKernelGenerationTest
