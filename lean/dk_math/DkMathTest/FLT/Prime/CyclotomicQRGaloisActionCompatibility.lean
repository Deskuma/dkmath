/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.CyclotomicQRGaloisActionProbe
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility"

namespace DkMathTest.FLT.Prime

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.TraceOneQuadratic

/-! The polynomial lift still reaches the existing p=11 norm axis. -/

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

/-! The same polynomial-to-norm compatibility is checked at p=13. -/

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

#print axioms eval_qrFactorPoly
#print axioms eval_qnrFactorPoly
#print axioms map_qrFactorPoly_to_qnr_of_nonsquare
#print axioms map_qnrFactorPoly_to_qr_of_nonsquare
#print axioms norm11
#print axioms norm13

end DkMathTest.FLT.Prime
