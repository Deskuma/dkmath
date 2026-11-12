import DkMath.FLT.FreyFiniteKernel

#print "file: Note032FiniteKernelSmoke"

/-! 005C₂a: 同じSource37の実点核、固定体、正規化関数と同じ零成分。 -/
namespace Note032FiniteKernelSmoke
open Module WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticFiniteKernel EllipticFunctionField
open EllipticTorsionRepresentation ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ実点核の固定体拡大次数は37。Sourceや直線の存在は仮定のまま。 -/
theorem source37_degree (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) :
    Module.finrank (kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L))
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 37 :=
  S.residual_kernelFixedField_finrank L hline

/-- 安定性だけで、同じ関数の固定体への所属と係数ガロア固定が得られる。 -/
theorem source37_stable_functions (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (hstable : IsStable S.residualRepresentation L) :
    (S.residualKernelX L hline ∈ kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L) ∧
      S.residualKernelY L hline ∈ kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve 37 L)) ∧
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelX L hline) = S.residualKernelX L hline ∧
      galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelY L hline) = S.residualKernelY L hline :=
  S.residual_kernel_coordinates_invariant L hline hstable

/-- Cofixed条件は同じ核の安定性を内部供給する。 -/
theorem source37_cofixed_functions (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) :
    galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelX L hline) = S.residualKernelX L hline ∧
      galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelY L hline) = S.residualKernelY L hline :=
  S.residual_cofixed_kernel_coordinates_galois L hline hcofixed σ

/-- 005AのL=E₀[37]を用い、固定体も同じ実点零成分の核のものへ接続する。
零成分の標的曲線への輸送やisogenyの存在を主張しない。 -/
theorem source37_zeroComponent_degree (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    pointSubgroup S.rationalCurve 37 L = pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A) ∧
    Module.finrank (kernelFixedField S.rationalCurve
      (pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A)))
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 37 := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hcofixed
  refine ⟨congrArg (pointSubgroup S.rationalCurve 37) heq, ?_⟩
  rw [← heq]
  exact S.residual_kernelFixedField_finrank L hline

end Note032FiniteKernelSmoke
