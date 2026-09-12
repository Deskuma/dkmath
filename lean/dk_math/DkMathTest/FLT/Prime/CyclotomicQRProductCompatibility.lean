/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.CyclotomicQRProductProbe
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
import DkMath.NumberTheory.CyclotomicQRProduct

#print "file: DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility"

namespace DkMathTest.FLT.Prime

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.NumberTheory.TraceOneQuadratic

/-! The promoted product theorem reaches the existing integer shell at `p=11`. -/

example (z y : ℤ) :
    (DkMath.NumberTheory.CyclotomicQRProduct.qrFinset 11).prod
        (fun a =>
          DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 11) a (z : ℂ) (y : ℂ)) *
      (DkMath.NumberTheory.CyclotomicQRProduct.qnrFinset 11).prod
        (fun a =>
          DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 11) a (z : ℂ) (y : ℂ)) =
    (norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) : ℂ) := by
  calc
    _ = GTailCyclotomicShell 11 ((z : ℂ) - (y : ℂ)) (y : ℂ) := by
      simpa using
        DkMath.NumberTheory.CyclotomicQRProduct.qr_qnr_product_eq_shell_endpoint
          (complexZeta 11)
          (complexZeta_isPrimitiveRoot (by norm_num)) (z : ℂ) (y : ℂ)
    _ = (GTailCyclotomicShell 11 (z - y) y : ℂ) := by
      simp [GTailCyclotomicShell]
    _ = (norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) : ℂ) := by
      simpa [GTailCyclotomicShell] using
        congrArg (fun n : ℤ => (n : ℂ)) (norm11 z y).symm

/-! The same shell/norm compatibility is checked at `p=13`. -/

example (z y : ℤ) :
    (DkMath.NumberTheory.CyclotomicQRProduct.qrFinset 13).prod
        (fun a =>
          DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 13) a (z : ℂ) (y : ℂ)) *
      (DkMath.NumberTheory.CyclotomicQRProduct.qnrFinset 13).prod
        (fun a =>
          DkMath.NumberTheory.CyclotomicQRProduct.rootFactor
            (complexZeta 13) a (z : ℂ) (y : ℂ)) =
    (norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) : ℂ) := by
  calc
    _ = GTailCyclotomicShell 13 ((z : ℂ) - (y : ℂ)) (y : ℂ) := by
      simpa using
        DkMath.NumberTheory.CyclotomicQRProduct.qr_qnr_product_eq_shell_endpoint
          (complexZeta 13)
          (complexZeta_isPrimitiveRoot (by norm_num)) (z : ℂ) (y : ℂ)
    _ = (GTailCyclotomicShell 13 (z - y) y : ℂ) := by
      simp [GTailCyclotomicShell]
    _ = (norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) : ℂ) := by
      simpa [GTailCyclotomicShell] using
        congrArg (fun n : ℤ => (n : ℂ)) (norm13 z y).symm

#print axioms DkMath.NumberTheory.CyclotomicQRProduct.qr_qnr_product_eq_shell_endpoint
#print axioms norm11
#print axioms norm13

end DkMathTest.FLT.Prime
