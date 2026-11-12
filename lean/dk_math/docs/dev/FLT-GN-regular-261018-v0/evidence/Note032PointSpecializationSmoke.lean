import DkMath.FLT.FreyFiniteKernelSpecialization

#print "file: Note032PointSpecializationSmoke"

/-! 同じSource37・同じ直線・同じ実点の特殊化。分離入力と標的楕円性入力を隠さない。 -/
namespace Note032PointSpecializationSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ実点の有限値が同じ標的モデルの方程式を満たす。 -/
theorem source37_equation (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve 37 L) :
    (S.residualKernelModel L hline).toAffine.Equation
      (S.residualKernelXAt L hline P hP) (S.residualKernelYAt L hline P hP) :=
  S.residual_kernel_at_equation L hline P hP

/-- 元の反転固定点から、標的2捩れ三次式の根への着地は内部供給済み。 -/
theorem source37_twoTorsion_root (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve)
    (hP : P ∉ pointSubgroup S.rationalCurve 37 L) (hneg : -P = P) :
    (S.residualKernelModel L hline).twoTorsionPolynomial.toPoly.eval
      (S.residualKernelXAt L hline P hP) = 0 :=
  S.residual_kernel_at_twoTorsion_root L hline P hP hneg

/-- 指数37では、同じ非零反転固定点が核の外にあることも内部供給できる。 -/
theorem source37_twoTorsion_outside (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (P : Points S.rationalCurve) (hP : P ≠ 0) (hneg : -P = P) :
    P ∉ pointSubgroup S.rationalCurve 37 L :=
  S.residual_twoTorsion_outside (by decide) L P hP hneg

/-- 残る三値の分離を入力した場合に、同じSource37の標的Δ≠0へ進む。 -/
theorem source37_discriminant_of_separation (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hline : Module.finrank (ZMod 37) L = 1)
    (P : Fin 3 → Points S.rationalCurve) (hP : ∀ i, P i ∉ pointSubgroup S.rationalCurve 37 L)
    (hneg : ∀ i, -P i = P i)
    (hx : Function.Injective (fun i => S.residualKernelXAt L hline (P i) (hP i))) :
    (S.residualKernelModel L hline).Δ ≠ 0 :=
  S.residual_kernel_model_discriminant_of_separation L hline P hP hneg hx

/-- 標的楕円性を保持した全点関数の零ファイバー。AddMonoidHom.kerではない。 -/
theorem source37_zero_fiber (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) [(S.residualKernelModel L hline).IsElliptic]
    (P : Points S.rationalCurve) :
    S.residualKernelPointMap L hline P = 0 ↔ P ∈ pointSubgroup S.rationalCurve 37 L :=
  S.residual_kernel_pointMap_eq_zero_iff L hline P

end Note032PointSpecializationSmoke
