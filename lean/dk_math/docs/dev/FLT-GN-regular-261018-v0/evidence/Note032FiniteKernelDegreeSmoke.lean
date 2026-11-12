import DkMath.FLT.FreyFiniteKernelDegree

#print "file: Note032FiniteKernelDegreeSmoke"

/-! 005C₂c₁: 同じSource37の有限次数、モニック関係、条件付き固定体生成。 -/
namespace Note032FiniteKernelDegreeSmoke
open Module WeierstrassCurve WeierstrassCurve.Affine IntermediateField Polynomial
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticTorsionRepresentation EllipticFiniteKernel ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ構成済み関数の単純部分体に対する有限性には追加providerを要求しない。 -/
theorem source37_finite (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    FiniteDimensional (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ∧
      FiniteDimensional (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField :=
  S.residual_kernel_function_degrees_finite L hline

/-- 同じSource上のY_Hは、同じX_Hの部分体上で実際の正次数モニック関係を持つ。 -/
theorem source37_monic_relation (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    ∃ q : ((AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯)[X],
      q.Monic ∧ 0 < q.natDegree ∧ aeval (S.residualKernelY L hline) q = 0 :=
  S.exists_residual_kernel_monic_relation L hline

/-- 次数74,111は仮定として明示する。供給された場合にだけ同じ固定体の生成を結論する。 -/
theorem source37_generation_of_degrees (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hX : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 74)
    (hY : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 111) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L) :=
  S.residual_kernel_coordinateField_eq_fixedField_of_degrees L hline hX hY

/-- 005Aの同じE₀[37]への接続でも、正確な次数と大域Cofixed性は仮定に残す。
零成分の標的への輸送やisogenyの存在は結論しない。 -/
theorem source37_zeroComponent_generation_of_degrees (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hX : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelX L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 74)
    (hY : Module.finrank (AlgebraicClosure ℚ)⟮S.residualKernelY L hline⟯
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 111) :
    adjoin (AlgebraicClosure ℚ) {S.residualKernelX L hline, S.residualKernelY L hline} =
      kernelFixedField S.rationalCurve
        (pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A)) := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hcofixed
  rw [← heq]
  exact S.residual_kernel_coordinateField_eq_fixedField_of_degrees L hline hX hY

end Note032FiniteKernelDegreeSmoke
