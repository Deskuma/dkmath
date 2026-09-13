/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaussNormalization

#print "file: DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationProbe"

namespace DkMathTest.FLT.Prime

open DkMath.NumberTheory.CyclotomicQRGaussNormalization
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.PrimeQuadraticDiscriminant

noncomputable section

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

private theorem gauss_square_normalization (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ SZ : MvPolynomial (Fin 2) ℤ,
      Dpoly (p := p) (cycloZeta p) ^ 2 =
        MvPolynomial.C (algebraMap ℤ (cycloField p)
          (signedPrimeDiscriminant p)) *
          (MvPolynomial.map (algebraMap ℤ (cycloField p)) SZ) ^ 2 := by
  exact exists_Dpoly_square_normalization hp2 (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

example : signedPrimeDiscriminant 3 = -3 := by norm_num [signedPrimeDiscriminant]
example : signedPrimeDiscriminant 5 = 5 := by norm_num [signedPrimeDiscriminant]
example : signedPrimeDiscriminant 7 = -7 := by norm_num [signedPrimeDiscriminant]
example : signedPrimeDiscriminant 11 = -11 := by norm_num [signedPrimeDiscriminant]
example : signedPrimeDiscriminant 13 = 13 := by norm_num [signedPrimeDiscriminant]

example : True := by
  obtain ⟨SZ, hSZ⟩ := gauss_square_normalization 3 (by norm_num)
  trivial

example : True := by
  obtain ⟨SZ, hSZ⟩ := gauss_square_normalization 5 (by norm_num)
  trivial

example : True := by
  obtain ⟨SZ, hSZ⟩ := gauss_square_normalization 7 (by norm_num)
  trivial

example : True := by
  obtain ⟨SZ, hSZ⟩ := gauss_square_normalization 11 (by norm_num)
  trivial

example : True := by
  obtain ⟨SZ, hSZ⟩ := gauss_square_normalization 13 (by norm_num)
  trivial

end

end DkMathTest.FLT.Prime
