/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.CyclotomicQRIntegralDescentProbe
import DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility

#print "file: DkMathTest.FLT.Prime.CyclotomicQRIntegralDescentCompatibility"

namespace DkMathTest.FLT.Prime

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRIntegralDescent
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private instance factPrime11Integral : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13Integral : Fact (Nat.Prime 13) := ⟨by norm_num⟩

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  letI : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

/-! The new integer witnesses and the existing p=11 shell/norm chain are
    checked together, without identifying the witnesses with A11/B11. -/

example :
    ∃ RZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ (cycloField 11)) RZ =
        Rpoly (p := 11) (cycloZeta 11) := by
  exact exists_Rpoly_over_int (cycloZeta 11) (cycloZeta_isPrimitiveRoot 11)

example :
    ∃ D2Z : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ (cycloField 13)) D2Z =
        Dpoly (p := 13) (cycloZeta 13) ^ 2 := by
  exact exists_Dpoly_sq_over_int (cycloZeta 13) (cycloZeta_isPrimitiveRoot 13)

example (z y : ℤ) :
    MvPolynomial.eval ![(z : ℂ), (y : ℂ)]
        (qrFactorPoly (p := 11) (complexZeta 11)) *
      MvPolynomial.eval ![(z : ℂ), (y : ℂ)]
        (qnrFactorPoly (p := 11) (complexZeta 11)) =
    (norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) : ℂ) := by
  calc
    _ = (DkMath.NumberTheory.CyclotomicQRProduct.qrFinset 11).prod
          (fun a => DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 11) a (z : ℂ) (y : ℂ)) *
        (DkMath.NumberTheory.CyclotomicQRProduct.qnrFinset 11).prod
          (fun a => DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 11) a (z : ℂ) (y : ℂ)) := by
      rw [eval_qrFactorPoly, eval_qnrFactorPoly]
    _ = GTailCyclotomicShell 11 ((z : ℂ) - (y : ℂ)) (y : ℂ) := by
      simpa [sub_add_cancel] using
        DkMath.NumberTheory.CyclotomicQRProduct.qr_qnr_product_eq_shell_endpoint
          (complexZeta 11)
          (complexZeta_isPrimitiveRoot (by norm_num)) (z : ℂ) (y : ℂ)
    _ = (GTailCyclotomicShell 11 (z - y) y : ℂ) := by
      simp [GTailCyclotomicShell]
    _ = (norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) : ℂ) := by
      simpa [GTailCyclotomicShell] using
        congrArg (fun n : ℤ => (n : ℂ)) (norm11 z y).symm

example (z y : ℤ) :
    MvPolynomial.eval ![(z : ℂ), (y : ℂ)]
        (qrFactorPoly (p := 13) (complexZeta 13)) *
      MvPolynomial.eval ![(z : ℂ), (y : ℂ)]
        (qnrFactorPoly (p := 13) (complexZeta 13)) =
    (norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) : ℂ) := by
  calc
    _ = (DkMath.NumberTheory.CyclotomicQRProduct.qrFinset 13).prod
          (fun a => DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 13) a (z : ℂ) (y : ℂ)) *
        (DkMath.NumberTheory.CyclotomicQRProduct.qnrFinset 13).prod
          (fun a => DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 13) a (z : ℂ) (y : ℂ)) := by
      rw [eval_qrFactorPoly, eval_qnrFactorPoly]
    _ = GTailCyclotomicShell 13 ((z : ℂ) - (y : ℂ)) (y : ℂ) := by
      simpa [sub_add_cancel] using
        DkMath.NumberTheory.CyclotomicQRProduct.qr_qnr_product_eq_shell_endpoint
          (complexZeta 13)
          (complexZeta_isPrimitiveRoot (by norm_num)) (z : ℂ) (y : ℂ)
    _ = (GTailCyclotomicShell 13 (z - y) y : ℂ) := by
      simp [GTailCyclotomicShell]
    _ = (norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) : ℂ) := by
      simpa [GTailCyclotomicShell] using
        congrArg (fun n : ℤ => (n : ℂ)) (norm13 z y).symm

end

end DkMathTest.FLT.Prime
