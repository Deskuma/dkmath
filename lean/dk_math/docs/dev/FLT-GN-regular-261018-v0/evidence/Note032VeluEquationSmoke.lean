import DkMath.FLT.FreyFiniteKernelDenominatorSupport

#print "file: Note032VeluEquationSmoke"

/-! Source37の同じ標的の無条件分母制御。方程式providerを入力に持たない。 -/
namespace Note032VeluEquationSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open WeierstrassRationalIntegralModel ValuationInertia
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じ37点核の候補と既存標的は等しい。 -/
theorem source37_same_model (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) :
    S.residualHalfKernelPolynomialModel L hl = S.residualKernelModel L hl :=
  S.residual_halfKernelPolynomialModel_eq (by decide) L hl

/-- 既存ℚ標的の実際の共通分母は37冪。方程式仮定なし。 -/
theorem source37_actual_denominator (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    ∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hl hs) = 37 ^ e :=
  S.residual_target_denominator_power (by decide) L hl hs

/-- 同じ既存標的の2進係数整性。2を例外に追加しない。 -/
theorem source37_dyadic_integral (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    CoeffIntegralAt (S.residualDescendedKernelModel L hl hs) 2 :=
  S.residual_target_coeffIntegralAt (by decide) L hl hs (by decide) (by decide)

/-- 任意の37以外の住所で、同じ整数化の倍率は単元。 -/
theorem source37_denominator_unit (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (hA : LiesOverPrime A q) :
    A.valuation (commonDenominator (S.residualDescendedKernelModel L hl hs) : AlgebraicClosure ℚ) = 1 :=
  S.residual_target_denominator_value_one (by decide) L hl hs A hq hqp hA

/-- 同じ整数標的と有理標的のΔ,c₄は、2進場所でも同じ付値。 -/
theorem source37_dyadic_invariants (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) =
        A.valuation ((S.residualDescendedKernelModel L hl hs).Δ : AlgebraicClosure ℚ) ∧
      A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) =
        A.valuation ((S.residualDescendedKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) :=
  S.residual_integer_target_invariant_values (by decide) L hl hs A (by decide) (by decide) hA

end Note032VeluEquationSmoke
