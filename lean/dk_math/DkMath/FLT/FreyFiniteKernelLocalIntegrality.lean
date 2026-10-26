/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelIntegralModel
import DkMath.FLT.FreyValuationArithmetic
import DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality
import DkMath.Lib.NumberTheory.WeierstrassDenominatorSupport

#print "file: DkMath.FLT.FreyFiniteKernelLocalIntegrality"

/-!
# 同じFrey核の局所整性と、同じ標的の分母支持の正確な境界

同じSourceの既存整数モデルから、p以外の全付値環に同じHの全座標を入れる。
反転対から一つずつ選んだ半核と分母なしVélu型多項式係数候補を構成し、その整性を証明する。
既存の同じℚ標的については、共通分母p冪と五係数の局所整性の同値を公開する。

候補の整性を、既存標的の整性と読み替えない。同じX_H,Y_Hが候補の方程式を満たすこと、
従ってkernelModel_uniqueで同じモデルに戻せることは、残る接続である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open WeierstrassVeluPolynomial WeierstrassRationalIntegralModel
open ValuationInertia ValuationPrimeSupport DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelLocalIntegrality {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ残余直線の実点核の全点は、実際にp倍で消える。 -/
theorem residual_kernel_killed (L : Submodule (ZMod p) S.ResidualSpace)
    (Q : pointSubgroup S.rationalCurve p L) : p • Q.val = 0 := by
  obtain ⟨T, _, he⟩ := Q.property
  have ht : p • T.val = 0 := T.property
  exact (congrArg (fun P : Points S.rationalCurve => p • P) he).symm.trans ht

/-- p以外の素数q上の全付値環に、同じ実点核の両座標が入る。Oも含める。 -/
theorem residual_kernel_coordinates_mem (L : Submodule (ZMod p) S.ResidualSpace)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) (Q : pointSubgroup S.rationalCurve p L) : Q.val.xc ∈ A ∧ Q.val.yc ∈ A := by
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := (p : ℤ)) (by
        intro hd; exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (by exact_mod_cast hd)))
  exact kernel_coordinates_mem S.rationalCurve _ p (S.residual_kernel_killed L) A (S.valuationModel A)
    (S.valuationModel_map A) hn Q

/-- 同じ一次元残余核の半核は、正確に(p−1)/2点。番号付けによる選択で生成元は不要。 -/
theorem card_residual_halfKernel (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    letI := S.finite_residualPointSubgroup L hline
    letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
    2 * (halfKernel S.rationalCurve (pointSubgroup S.rationalCurve p L)).card + 1 = p := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact (card_halfKernel S.rationalCurve _ (S.residual_pointSubgroup_odd hp2 L hline)).trans
    (card_pointSubgroup S.rationalCurve p L hline)

/-- 同じ半核を添字とする多項式係数候補。既存の標的との一致を定義に含めない。 -/
noncomputable def residualHalfKernelPolynomialModel
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1) :
    WeierstrassCurve (AlgebraicClosure ℚ) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact halfKernelPolynomialModel S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 同じ半核による多項式係数候補は、p以外の全付値環で五係数が整。
既存kernelModelとの同一性は入力にも結論にも隠さない。 -/
theorem residual_halfKernelPolynomialModel_coefficientsIn
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) : CoefficientsIn A.toSubring (S.residualHalfKernelPolynomialModel L hline) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hn : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := (p : ℤ)) (by
        intro hd; exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (by exact_mod_cast hd)))
  exact halfKernelPolynomialModel_coefficientsIn S.rationalCurve _ p (S.residual_kernel_killed L)
    A (S.valuationModel A) (S.valuationModel_map A) hn

/-- 既存の同じℚ標的の共通分母がp冪であることは、その五係数がp以外で整であることと同値。
右辺の一般証明は未供給であり、上の多項式候補の整性だけでは右辺を結論しない。 -/
theorem residual_target_denominator_power_iff
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hline hstable) = p ^ e) ↔
      ∀ q : ℕ, q.Prime → q ≠ p → CoeffIntegralAt (S.residualDescendedKernelModel L hline hstable) q :=
  exists_commonDenominator_pow_iff _ Fact.out

/-- 同じ二関数の方程式という一つの未証明入力から、既存標的の局所整性まで接続する。
候補係数の整性・標的の一意性・元のℚモデルへの降下・素数住所の存在を全て内部供給する。 -/
theorem residual_target_coeffIntegralAt_of_polynomial_equation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (he : ((S.residualHalfKernelPolynomialModel L hline).toAffine⁄(S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
        (S.residualKernelX L hline) (S.residualKernelY L hline))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    CoeffIntegralAt (S.residualDescendedKernelModel L hline hstable) q := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have heq : S.residualHalfKernelPolynomialModel L hline = S.residualKernelModel L hline :=
    halfKernelPolynomialModel_eq_kernelModel_of_equation S.rationalCurve _ he
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) hq
  have hc := S.residual_halfKernelPolynomialModel_coefficientsIn L hline hq hqp A hA
  rw [heq, ← S.residual_descended_kernel_model_map L hline hstable] at hc
  apply (coeffIntegralAt_iff_mem _ A hq ((ValuationSubring.mem_nonunits_iff _).mp hA)).mpr
  exact hc

/-- 同じ具体的方程式が証明されれば、既存の同じ共通分母がp冪であることまで一括して閉じる。
方程式仮定は未解消であり、無条件の分母支持定理とは区別する。 -/
theorem residual_target_denominator_power_of_polynomial_equation
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (he : ((S.residualHalfKernelPolynomialModel L hline).toAffine⁄(S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
        (S.residualKernelX L hline) (S.residualKernelY L hline)) :
    ∃ e : ℕ, commonDenominator (S.residualDescendedKernelModel L hline hstable) = p ^ e :=
  (S.residual_target_denominator_power_iff L hline hstable).mpr
    (fun _ hq hqp => S.residual_target_coeffIntegralAt_of_polynomial_equation L hline hstable he hq hqp)

end DkMath.FLT.Frey.Source
