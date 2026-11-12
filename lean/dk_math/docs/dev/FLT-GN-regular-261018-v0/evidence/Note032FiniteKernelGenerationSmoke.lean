import DkMath.FLT.FreyFiniteKernelGeneration

#print "file: Note032FiniteKernelGenerationSmoke"

/-! 同じSource37の次数・固定体生成・二次関係。前回の次数74,111の入力を除去する。 -/
namespace Note032FiniteKernelGenerationSmoke
open Polynomial IntermediateField Module WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticFiniteKernel EllipticTorsionRepresentation ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource・同じ直線の二関数の次数74,111を内部計算する。 -/
theorem source37_degrees (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 74 ∧
    Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 111 :=
  S.residual_kernel_function_degrees L hline

/-- 同じSource37上の固定体生成を、次数の仮定なしで閉じる。 -/
theorem source37_generation (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L) :=
  S.residual_kernel_coordinateField_eq_fixedField L hline

/-- 同じSource37のモニック二次関係。係数体は同じk(X_H)である。 -/
theorem source37_quadratic (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    ∃ q : ((AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯)[X],
      q.Monic ∧ q.natDegree = 2 ∧ aeval (S.residualKernelY L hline) q = 0 :=
  S.exists_residual_kernel_quadratic_relation L hline

/-- 同じY_Hの最小多項式の二次性も、存在関係だけでなく確認する。 -/
theorem source37_minpoly (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    (minpoly (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
      (S.residualKernelY L hline)).natDegree = 2 :=
  S.natDegree_residual_kernel_minpoly L hline

/-- 同じE₀[37]との接続では、大域Cofixed性だけを引き続き保持する。
次数74,111の入力は消去済み。標的の零成分への輸送を結論するものではない。 -/
theorem source37_same_zeroComponent_generation (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve
        (pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A)) := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hcofixed
  rw [← heq]
  exact S.residual_kernel_coordinateField_eq_fixedField L hline

end Note032FiniteKernelGenerationSmoke
