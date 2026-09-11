/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.TraceOneDiscriminantAxis
import DkMath.Lib.Cosmic.GTailCyclotomic

#print "file: DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.TraceOneQuadratic

/-! ## The explicit `p = 11` probe -/

def A11 (z y : ℤ) : ℤ :=
  z ^ 5 - z ^ 3 * y ^ 2 + z ^ 2 * y ^ 3 - z * y ^ 4 - y ^ 5

def B11 (z y : ℤ) : ℤ := z ^ 4 * y + z * y ^ 4

def R11 (z y : ℤ) : ℤ := 2 * A11 z y + B11 z y

def S11 (z y : ℤ) : ℤ := B11 z y

theorem endpoint11 (z y : ℤ) : (z - y) + y = z := by ring

theorem parity11 (z y : ℤ) : R11 z y - S11 z y = 2 * A11 z y := by
  simp [R11, S11]

theorem discr_neg_three : discr (-3) = -11 := by norm_num [discr]

theorem gauss_form11 (z y : ℤ) :
    4 * GTailCyclotomicShell 11 (z - y) y =
      R11 z y ^ 2 - (-11 : ℤ) * S11 z y ^ 2 := by
  norm_num [R11, S11, A11, B11, GTailCyclotomicShell,
    Finset.sum_range_succ]
  ring

theorem norm11_direct (z y : ℤ) :
    norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) =
      GTailCyclotomicShell 11 (z - y) y := by
  norm_num [A11, B11, DkMath.NumberTheory.TraceOneQuadratic.norm,
    GTailCyclotomicShell, Finset.sum_range_succ]
  ring

theorem norm11 (z y : ℤ) :
    norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) =
      GTailCyclotomicShell 11 (z - y) y := by
  apply norm_eq_of_gauss_coordinates (R := R11 z y) (S := S11 z y)
  · rfl
  · simpa [discr_neg_three] using gauss_form11 z y

theorem norm11_expanded (z y : ℤ) :
    norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) =
      z ^ 10 + z ^ 9 * y + z ^ 8 * y ^ 2 + z ^ 7 * y ^ 3 +
      z ^ 6 * y ^ 4 + z ^ 5 * y ^ 5 + z ^ 4 * y ^ 6 +
      z ^ 3 * y ^ 7 + z ^ 2 * y ^ 8 + z * y ^ 9 + y ^ 10 := by
  norm_num [A11, B11, DkMath.NumberTheory.TraceOneQuadratic.norm,
    GTailCyclotomicShell, Finset.sum_range_succ]
  ring

/-! ## The explicit `p = 13` probe -/

def A13 (z y : ℤ) : ℤ :=
  z ^ 6 + 2 * z ^ 4 * y ^ 2 - z ^ 3 * y ^ 3 +
    2 * z ^ 2 * y ^ 4 + y ^ 6

def B13 (z y : ℤ) : ℤ := z ^ 5 * y + z ^ 3 * y ^ 3 + z * y ^ 5

def R13 (z y : ℤ) : ℤ := 2 * A13 z y + B13 z y

def S13 (z y : ℤ) : ℤ := B13 z y

theorem endpoint13 (z y : ℤ) : (z - y) + y = z := by ring

theorem parity13 (z y : ℤ) : R13 z y - S13 z y = 2 * A13 z y := by
  simp [R13, S13]

theorem discr_three : discr 3 = 13 := by norm_num [discr]

theorem gauss_form13 (z y : ℤ) :
    4 * GTailCyclotomicShell 13 (z - y) y =
      R13 z y ^ 2 - (13 : ℤ) * S13 z y ^ 2 := by
  norm_num [R13, S13, A13, B13, GTailCyclotomicShell,
    Finset.sum_range_succ]
  ring

theorem norm13_direct (z y : ℤ) :
    norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) =
      GTailCyclotomicShell 13 (z - y) y := by
  norm_num [A13, B13, DkMath.NumberTheory.TraceOneQuadratic.norm,
    GTailCyclotomicShell, Finset.sum_range_succ]
  ring

theorem norm13 (z y : ℤ) :
    norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) =
      GTailCyclotomicShell 13 (z - y) y := by
  apply norm_eq_of_gauss_coordinates (R := R13 z y) (S := S13 z y)
  · rfl
  · exact gauss_form13 z y

theorem norm13_expanded (z y : ℤ) :
    norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) =
      z ^ 12 + z ^ 11 * y + z ^ 10 * y ^ 2 + z ^ 9 * y ^ 3 +
      z ^ 8 * y ^ 4 + z ^ 7 * y ^ 5 + z ^ 6 * y ^ 6 +
      z ^ 5 * y ^ 7 + z ^ 4 * y ^ 8 + z ^ 3 * y ^ 9 +
      z ^ 2 * y ^ 10 + z * y ^ 11 + y ^ 12 := by
  norm_num [A13, B13, DkMath.NumberTheory.TraceOneQuadratic.norm,
    GTailCyclotomicShell, Finset.sum_range_succ]
  ring

#print axioms norm11
#print axioms norm13
#print axioms gauss_form11
#print axioms gauss_form13

end DkMathTest.FLT.Prime
