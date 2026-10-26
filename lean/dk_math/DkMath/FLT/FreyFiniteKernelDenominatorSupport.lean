/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelLocalIntegrality
import DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation

#print "file: DkMath.FLT.FreyFiniteKernelDenominatorSupport"

/-!
# 同じFrey標的の無条件p冪分母と、p以外での整数化の付値保存

前段の条件付きAPIの方程式入力を、同じX_H,Y_Hについて内部証明した。
同じSource、直線L、実点核H、既存ℚ標的、既存整数モデルを一つも取り替えない。
ここで比較するΔ,c₄は標的の整数化前後であり、源と商の局所還元比較ではない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open WeierstrassRationalIntegralModel ValuationInertia
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelDenominatorSupport {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSourceのX_H,Y_Hは同じ半核候補の方程式を満たす。p≠2から奇数性を内部供給。 -/
theorem residual_halfKernelPolynomialModel_equation (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1) :
    ((S.residualHalfKernelPolynomialModel L hl).toAffine⁄(S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation (S.residualKernelX L hl) (S.residualKernelY L hl) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact halfKernelPolynomialModel_equation S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hl)

/-- 半核の明示的候補は、既存の同じSource標的と一致する。別の楕円曲線を選び直さない。 -/
theorem residual_halfKernelPolynomialModel_eq (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1) :
    S.residualHalfKernelPolynomialModel L hl = S.residualKernelModel L hl := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact halfKernelPolynomialModel_eq_kernelModel S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hl)

/-- 同じ安定核から降下した既存ℚ標的の五係数は、p以外の全素数で整。 -/
theorem residual_target_coeffIntegralAt (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    CoeffIntegralAt (S.residualDescendedKernelModel L hl hs) q :=
  S.residual_target_coeffIntegralAt_of_polynomial_equation L hl hs
    (S.residual_halfKernelPolynomialModel_equation hp2 L hl) hq hqp

/-- 既存の同じℚ標的の実際の共通分母はp冪。未証明の方程式入力は残さない。 -/
theorem residual_target_denominator_power (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) :
    ∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hl hs) = p ^ e :=
  S.residual_target_denominator_power_of_polynomial_equation L hl hs
    (S.residual_halfKernelPolynomialModel_equation hp2 L hl)

/-- p以外の素数住所で、同じ既存整数化の倍率は単元。 -/
theorem residual_target_denominator_value_one {K : Type*} [Field K] [CharZero K]
    (hp2 : p ≠ 2) (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) (A : ValuationSubring K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hA : LiesOverPrime A q) :
    A.valuation (commonDenominator (S.residualDescendedKernelModel L hl hs) : K) = 1 :=
  commonDenominator_value_one _ A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (S.residual_target_coeffIntegralAt hp2 L hl hs hq hqp)

/-- 同じ整数標的と同じℚ標的のΔ,c₄は、p以外の素数住所で付値が一致する。
元のFrey源と商標的の比較や最小性は、この定理の結論には含めない。 -/
theorem residual_integer_target_invariant_values {K : Type*} [Field K] [CharZero K]
    (hp2 : p ≠ 2) (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) (A : ValuationSubring K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hA : LiesOverPrime A q) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : K) =
        A.valuation ((S.residualDescendedKernelModel L hl hs).Δ : K) ∧
      A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : K) =
        A.valuation ((S.residualDescendedKernelModel L hl hs).c₄ : K) :=
  integerModel_invariants_of_coeffIntegralAt _ A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (S.residual_target_coeffIntegralAt hp2 L hl hs hq hqp)

end DkMath.FLT.Frey.Source
