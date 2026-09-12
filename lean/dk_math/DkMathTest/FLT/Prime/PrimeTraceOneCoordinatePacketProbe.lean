/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.FLT.Seven.PrimitiveCoordinateCoprime
import DkMath.FLT.Seven.QuadraticBridge
import DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneCoordinatePacketProbe"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.FLT.Seven
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

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-! p=3 retains the first odd-prime/Eisenstein parameter without asserting a
generic axis-stripping conclusion. -/

example : signedPrimeParameter 3 = -1 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 3) (p := 3) (by norm_num)
    (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3)
  have h := P.coord_norm_eq 1 0
  trivial

/-! p=5 exercises the `TraceOneInt 1` coordinate packet and the numerical
p-adic exclusion at the smallest real odd-prime parameter. -/

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 5) (p := 5) (by norm_num)
    (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5)
  have h := P.coord_norm_eq 1 0
  norm_num [GTailCyclotomicShell, Finset.sum_range_succ] at h
  trivial

/-! p=7 compares the generic packet endpoint to the established specialized
cyclotomic-seven coordinate endpoint. -/

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 7) (p := 7) (by norm_num)
    (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7)
  have hgeneric :
      norm (P.coord 2 1) = GTailCyclotomicShell 7 (2 - 1) 1 :=
    P.coord_norm_eq 2 1
  have hspecial :
      norm (cyclotomicSevenToTraceOne 2 1) =
        GTailCyclotomicShell 7 (2 - 1) 1 := by
    rw [← cyclotomicSeven_eq_traceOneNorm_negTwo]
    norm_num [cyclotomicSeven, GTailCyclotomicShell, Finset.sum_range_succ]
  have hcompare :
      norm (P.coord 2 1) = norm (cyclotomicSevenToTraceOne 2 1) :=
    hgeneric.trans hspecial.symm
  have hspecial_coprime :
      IsCoprime (cyclotomicSevenToTraceOne 2 1).fst
        (cyclotomicSevenToTraceOne 2 1).snd := by
    simpa [cyclotomicSevenToTraceOne] using
      (cyclotomicSeven_coordinates_isCoprime (z := 2) (y := 1) (by norm_num))
  exact True.intro

/-! The explicit p=11 and p=13 formula probes are compared with the generic
packet through their common exact shell norm endpoint. -/

example (z y : ℤ) : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 11) (p := 11) (by norm_num)
    (cycloZeta 11) (cycloZeta_isPrimitiveRoot 11)
  have hgeneric := P.coord_norm_eq z y
  have hexplicit := norm11 z y
  have hcompare : norm (P.coord z y) = norm (⟨A11 z y, B11 z y⟩ : TraceOneInt (-3)) :=
    hgeneric.trans hexplicit.symm
  exact True.intro

example (z y : ℤ) : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 13) (p := 13) (by norm_num)
    (cycloZeta 13) (cycloZeta_isPrimitiveRoot 13)
  have hgeneric := P.coord_norm_eq z y
  have hexplicit := norm13 z y
  have hcompare : norm (P.coord z y) = norm (⟨A13 z y, B13 z y⟩ : TraceOneInt 3) :=
    hgeneric.trans hexplicit.symm
  exact True.intro

end

end DkMathTest.FLT.Prime
