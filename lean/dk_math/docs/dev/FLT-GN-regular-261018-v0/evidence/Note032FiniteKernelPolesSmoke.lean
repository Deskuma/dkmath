import DkMath.FLT.FreyFiniteKernelPoles

#print "file: Note032FiniteKernelPolesSmoke"

/-! 005C₂b: 同じSource37の構成済み二関数の非定数性と極の支持。 -/
namespace Note032FiniteKernelPolesSmoke
open Module WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory EllipticTorsionRepresentation ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceと直線から構成した二関数は、全ての代数的定数と異なる。 -/
theorem source37_nonconstant (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (c : AlgebraicClosure ℚ) :
    S.residualKernelX L hline ≠ algebraMap (AlgebraicClosure ℚ)
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c ∧
      S.residualKernelY L hline ≠ algebraMap (AlgebraicClosure ℚ)
        (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField c :=
  S.residual_kernel_coordinates_nonconstant L hline c

/-- 同じ残余点P∈Lを実点群へ戻しても、同じ二関数の極の値を得る。 -/
theorem source37_line_point_poles (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (P : S.ResidualSpace) (hP : P ∈ L) :
    pointValuation S.rationalCurve P.val (S.residualKernelX L hline) = exp (2 : ℤ) ∧
      pointValuation S.rationalCurve P.val (S.residualKernelY L hline) = exp (3 : ℤ) :=
  S.residual_kernel_coordinate_valuations_of_mem L hline P.val ⟨P, hP, rfl⟩

/-- 二関数の極の支持は、同じSourceの同じ直線の実点像である。 -/
theorem source37_pole_support (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : finrank (ZMod 37) L = 1) (P : Points S.rationalCurve) :
    (1 < pointValuation S.rationalCurve P (S.residualKernelX L hline) ↔
      P ∈ pointSubgroup S.rationalCurve 37 L) ∧
    (1 < pointValuation S.rationalCurve P (S.residualKernelY L hline) ↔
      P ∈ pointSubgroup S.rationalCurve 37 L) :=
  S.residual_kernel_coordinate_pole_support L hline P

/-- 大域Cofixed直線の入力を保持し、005Aの同定で同じE₀[37]の実点像へ接続する。
Frey曲線の2進零成分と、関数体の点付値による極の概念は別である。 -/
theorem source37_zeroComponent_pole_support (S : Source 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : finrank (ZMod 37) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) (P : Points S.rationalCurve) :
    (1 < pointValuation S.rationalCurve P (S.residualKernelX L hline) ↔
      P ∈ pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A)) ∧
    (1 < pointValuation S.rationalCurve P (S.residualKernelY L hline) ↔
      P ∈ pointSubgroup S.rationalCurve 37 (S.residualZeroComponent A)) := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two (by decide) A hA L hline hcofixed
  rw [← heq]
  exact S.residual_kernel_coordinate_pole_support L hline P

end Note032FiniteKernelPolesSmoke
