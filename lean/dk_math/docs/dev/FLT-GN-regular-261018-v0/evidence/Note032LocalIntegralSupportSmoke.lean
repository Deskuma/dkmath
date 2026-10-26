import DkMath.FLT.FreyFiniteKernelLocalIntegrality

#print "file: Note032LocalIntegralSupportSmoke"

/-! Source37の同じHの整性と、未証明方程式を明示した分母支持への接続。 -/
namespace Note032LocalIntegralSupportSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open WeierstrassVeluPolynomial WeierstrassRationalIntegralModel
open DkMath.Lib.RepresentationTheory ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じHの全点は37倍で消える。 -/
theorem source37_kernel_killed (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (Q : pointSubgroup S.rationalCurve 37 L) : 37 • Q.val = 0 :=
  S.residual_kernel_killed L Q

/-- 2進場所も例外にせず、同じ実点核の全座標が整になる。 -/
theorem source37_kernel_integral_at_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (Q : pointSubgroup S.rationalCurve 37 L) : Q.val.xc ∈ A ∧ Q.val.yc ∈ A :=
  S.residual_kernel_coordinates_mem L (by decide) (by decide) A hA Q

/-- 同じ37点核の半核は18点。 -/
theorem source37_half_card (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) :
    letI := S.finite_residualPointSubgroup L hl
    letI := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
    (EllipticFiniteKernel.halfKernel S.rationalCurve (pointSubgroup S.rationalCurve 37 L)).card = 18 := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
  have he := S.card_residual_halfKernel (by decide) L hl
  omega

/-- 同じ18代表による多項式係数候補は、2進場所でも整。 -/
theorem source37_candidate_integral_at_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    CoefficientsIn A.toSubring (S.residualHalfKernelPolynomialModel L hl) :=
  S.residual_halfKernelPolynomialModel_coefficientsIn L hl (by decide) (by decide) A hA

/-- 既存標的の実際の共通分母に対する判定。右辺の無条件証明は含まない。 -/
theorem source37_actual_denominator_criterion (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    (hs : IsStable S.residualRepresentation L) :
    (∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hl hs) = 37 ^ e) ↔
      ∀ q : ℕ, q.Prime → q ≠ 37 → CoeffIntegralAt (S.residualDescendedKernelModel L hl hs) q :=
  S.residual_target_denominator_power_iff L hl hs

/-- 未証明の同じ二関数の方程式を明示して保持した、実際の37冪分母への接続。 -/
theorem source37_conditional_denominator_power (S : Source 37)
    (L : Submodule (ZMod 37) S.ResidualSpace) (hl : Module.finrank (ZMod 37) L = 1)
    (hs : IsStable S.residualRepresentation L)
    (he : ((S.residualHalfKernelPolynomialModel L hl).toAffine⁄(S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation (S.residualKernelX L hl) (S.residualKernelY L hl)) :
    ∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hl hs) = 37 ^ e :=
  S.residual_target_denominator_power_of_polynomial_equation L hl hs he

end Note032LocalIntegralSupportSmoke
