/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge

#print "file: DkMathTest.FLT.Prime.CyclotomicQRTraceOneBridgeProbe"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

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

private theorem primeTraceOneBridge (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ AZ SZ : MvPolynomial (Fin 2) ℤ,
      ∀ z y : ℤ,
        norm
          (⟨MvPolynomial.eval ![z, y] AZ,
             MvPolynomial.eval ![z, y] SZ⟩ :
            TraceOneInt (signedPrimeParameter p)) =
          GTailCyclotomicShell p (z - y) y := by
  exact exists_prime_traceOne_coordinates hp2 (cycloZeta p)
    (cycloZeta_isPrimitiveRoot p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

example : signedPrimeParameter 3 = -1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 5 = 1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 11 = -3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 13 = 3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : True := by
  obtain ⟨AZ, SZ, hbridge⟩ := primeTraceOneBridge 3 (by norm_num)
  have := hbridge 1 0
  trivial

example : True := by
  obtain ⟨AZ, SZ, hbridge⟩ := primeTraceOneBridge 5 (by norm_num)
  have := hbridge 1 0
  trivial

example : True := by
  obtain ⟨AZ, SZ, hbridge⟩ := primeTraceOneBridge 7 (by norm_num)
  have := hbridge 1 0
  trivial

example : True := by
  obtain ⟨AZ, SZ, hbridge⟩ := primeTraceOneBridge 11 (by norm_num)
  have := hbridge 1 0
  trivial

example : True := by
  obtain ⟨AZ, SZ, hbridge⟩ := primeTraceOneBridge 13 (by norm_num)
  have := hbridge 1 0
  trivial

end

end DkMathTest.FLT.Prime
