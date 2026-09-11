/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationProbe
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationCompatibility"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRGaussNormalization
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private instance factPrime11Compat : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13Compat : Fact (Nat.Prime 13) := ⟨by norm_num⟩

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

example : signedPrimeDiscriminant 11 = -11 := by
  norm_num [signedPrimeDiscriminant]

example : signedPrimeDiscriminant 13 = 13 := by
  norm_num [signedPrimeDiscriminant]

example : discr (signedPrimeParameter 11) = -11 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

example : discr (signedPrimeParameter 13) = 13 := by
  exact discr_signedPrimeParameter (by norm_num) (by norm_num)

/-! The existential witnesses are intentionally not identified with the
    explicit `B11`/`B13` witnesses. -/

example : True := by
  obtain ⟨SZ, hSZ⟩ :=
    exists_Dpoly_square_normalization (L := cycloField 11) (p := 11)
      (by norm_num) (cycloZeta 11) (cycloZeta_isPrimitiveRoot 11)
  have hcompat :
      Dpoly (p := 11) (cycloZeta 11) ^ 2 =
        MvPolynomial.C ((-11 : ℤ) : cycloField 11) *
          (MvPolynomial.map (Int.castRingHom (cycloField 11)) SZ) ^ 2 := by
    simpa [signedPrimeDiscriminant] using hSZ
  trivial

example : True := by
  obtain ⟨SZ, hSZ⟩ :=
    exists_Dpoly_square_normalization (L := cycloField 13) (p := 13)
      (by norm_num) (cycloZeta 13) (cycloZeta_isPrimitiveRoot 13)
  have hcompat :
      Dpoly (p := 13) (cycloZeta 13) ^ 2 =
        MvPolynomial.C ((13 : ℤ) : cycloField 13) *
          (MvPolynomial.map (Int.castRingHom (cycloField 13)) SZ) ^ 2 := by
    simpa [signedPrimeDiscriminant] using hSZ
  trivial

/-! Existing explicit p=11/p=13 TraceOne square regressions remain green. -/

example (z y : ℤ) :
    4 * GTailCyclotomicShell 11 (z - y) y =
      R11 z y ^ 2 - (-11 : ℤ) * S11 z y ^ 2 := by
  exact gauss_form11 z y

example (z y : ℤ) :
    4 * GTailCyclotomicShell 13 (z - y) y =
      R13 z y ^ 2 - (13 : ℤ) * S13 z y ^ 2 := by
  exact gauss_form13 z y

end

end DkMathTest.FLT.Prime
