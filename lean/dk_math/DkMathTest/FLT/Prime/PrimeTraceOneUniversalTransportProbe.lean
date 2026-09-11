/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
import DkMath.FLT.Seven.PrimitiveCoordinateCoprime

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportProbe"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.FLT.Seven
open DkMath.NumberTheory.CyclotomicQRUniversalTransport
open DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor
open DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private abbrev probeField (p : ℕ) := CyclotomicField p ℚ

private instance probeField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (probeField p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  letI : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def probeZeta (p : ℕ) [Fact p.Prime] : probeField p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (probeField p)

private theorem probeZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (probeZeta p) p := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (probeField p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-! p=3 covers the universal-R transport API while retaining the separate
Eisenstein exception boundary. -/

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := probeField 3) (p := 3) (by norm_num)
    (probeZeta 3) (probeZeta_isPrimitiveRoot 3)
  have hR := phase22_RZ_anchor_eq_universal P
  have hcoord := P.coord_norm_eq 1 0
  trivial

/-! p=5 exercises the odd common-prime support theorem. -/

example {q z y : ℕ} [Fact q.Prime]
    (P : PrimeTraceOneCoordinatePacket (probeField 5) 5
      (probeZeta 5) (probeZeta_isPrimitiveRoot 5))
    (hcop : Nat.Coprime z y)
    (hA : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    q = 5 ∨ q = 2 :=
  common_coordinate_prime_eq_exponent_or_two P hcop hA hS

/-! p=7 compares the generic conditional FLT-side endpoint with the existing
specialized primitive-coordinate theorem. -/

example {g u x : ℕ}
    (P0 : PrimeAdicFactorPacket 7 g u x) :
    IsCoprime
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)]
        (Classical.choice (exists_prime_traceOne_coordinate_packet
          (L := probeField 7) (p := 7) (by norm_num)
          (probeZeta 7) (probeZeta_isPrimitiveRoot 7))).AZ)
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)]
        (Classical.choice (exists_prime_traceOne_coordinate_packet
          (L := probeField 7) (p := 7) (by norm_num)
          (probeZeta 7) (probeZeta_isPrimitiveRoot 7))).SZ) := by
  let P := Classical.choice (exists_prime_traceOne_coordinate_packet
    (L := probeField 7) (p := 7) (by norm_num)
    (probeZeta 7) (probeZeta_isPrimitiveRoot 7))
  exact prime_packet_coordinate_isCoprime P0 P

example {z y : ℕ} (hcop : Nat.Coprime z y) :
    IsCoprime (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)).fst
      (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ)).snd :=
  cyclotomicSeven_coordinates_isCoprime hcop

/-! p=11 and p=13 keep the imaginary and real TraceOne carrier probes. -/

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := probeField 11) (p := 11) (by norm_num)
    (probeZeta 11) (probeZeta_isPrimitiveRoot 11)
  have hR := phase22_RZ_anchor_eq_universal P
  trivial

example : True := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := probeField 13) (p := 13) (by norm_num)
    (probeZeta 13) (probeZeta_isPrimitiveRoot 13)
  have hR := phase22_RZ_anchor_eq_universal P
  trivial

end

end DkMathTest.FLT.Prime
