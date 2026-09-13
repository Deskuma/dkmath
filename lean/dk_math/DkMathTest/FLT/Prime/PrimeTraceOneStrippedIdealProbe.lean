/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
import DkMath.FLT.Seven.QuadraticBridge
import DkMath.FLT.Seven.QuadraticResidualPacket

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealProbe"

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

private theorem generic_endpoint
    {p g u x : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket p g u x) :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField p) p
        (cycloZeta p) (cycloZeta_isPrimitiveRoot p),
      Nonempty (DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket
        (cycloField p) P0 P) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField p) (p := p) hp2
    (cycloZeta p) (cycloZeta_isPrimitiveRoot p)
  exact ⟨P, DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket P0 P⟩

/-! The p=3 regression checks the generic bridge only; it does not assert a
singleton unit sector or an FLT conclusion. -/
example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 3 g u x) : True := by
  have hs : signedPrimeParameter 3 = -1 := by
    norm_num [signedPrimeParameter, signedPrimeDiscriminant]
  obtain ⟨P, hP⟩ := generic_endpoint (p := 3) (by norm_num) P0
  have hpacket := hP
  trivial

/-! The p=5 regression exercises the `TraceOneInt 1` carrier. -/
example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 5 g u x) : True := by
  have hs : signedPrimeParameter 5 = 1 := by
    norm_num [signedPrimeParameter, signedPrimeDiscriminant]
  obtain ⟨P, hP⟩ := generic_endpoint (p := 5) (by norm_num) P0
  have hpacket := hP
  trivial

/-! The p=7 regression keeps the generic output conditional and separately
replays the established specialized residual norm-power endpoint. -/
example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 7 g u x) : True := by
  have hs : signedPrimeParameter 7 = -2 := by
    norm_num [signedPrimeParameter, signedPrimeDiscriminant]
  obtain ⟨P, hP⟩ := generic_endpoint (p := 7) (by norm_num) P0
  have hpacket := hP
  trivial

example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ b : ℕ, norm q.residualCore = (b : ℤ) ^ 7 :=
  q.norm_is_seventh_power

/-! The p=11 and p=13 regressions exercise the negative and positive signed
prime TraceOne carriers without making a global FLT claim. -/
example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 11 g u x) : True := by
  have hs : signedPrimeParameter 11 = -3 := by
    norm_num [signedPrimeParameter, signedPrimeDiscriminant]
  obtain ⟨P, hP⟩ := generic_endpoint (p := 11) (by norm_num) P0
  have hpacket := hP
  trivial

example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 13 g u x) : True := by
  have hs : signedPrimeParameter 13 = 3 := by
    norm_num [signedPrimeParameter, signedPrimeDiscriminant]
  obtain ⟨P, hP⟩ := generic_endpoint (p := 13) (by norm_num) P0
  have hpacket := hP
  trivial

end

end DkMathTest.FLT.Prime
