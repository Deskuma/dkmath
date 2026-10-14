/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.PrimeGaugeBridge

#print "file: DkMathTest.FLT.Prime.PrimeGaugeBridge"

namespace DkMathTest.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.NumberTheory.Gauge
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Exponent gauges and homogeneous evaluation -/

example : PrimeExponentGauge 3 := by
  exact primeExponentGauge_of_prime (by norm_num)

example : PrimeExponentGauge 5 := by
  exact primeExponentGauge_of_prime (by norm_num)

example : PrimeExponentGauge 7 := by
  exact primeExponentGauge_of_prime (by norm_num)

example (x u : ℤ) :
    GTail 3 1 x u =
      GTailCyclotomicHomEval 3 (Polynomial.cyclotomic 3 ℤ) x u := by
  exact primeExponentGauge_GTail_eq_cyclotomicHomEval
    (primeExponentGauge_of_prime (by norm_num)) x u

/-! ## Ideal and ValueGauge resolution -/

example (g u : ℕ) :
    Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (cycloZeta_isPrimitiveRoot 3) g u) =
      GTail 3 1 g u := by
  exact primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail
    (primeExponentGauge_of_prime (by norm_num))
    (cycloZeta_isPrimitiveRoot 3)

example (g u n : ℕ) :
    valueGaugeCoordinates n
        (Ideal.absNorm
          (cyclotomicLinearFactorIdeal
            (cycloZeta_isPrimitiveRoot 5) g u)) =
      valueGaugeCoordinates n (GTail 5 1 g u) := by
  exact primeExponentGauge_valueGaugeCoordinates_cyclotomicIdeal_eq_GTail
    (primeExponentGauge_of_prime (by norm_num))
    (cycloZeta_isPrimitiveRoot 5) n

/-! ## TraceOne scalar transport -/

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 3) 3
        (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3),
      valueGaugeCoordinates 3
          (Int.natAbs (norm (P.coord ((2 + 1 : ℕ) : ℤ) (1 : ℤ)))) =
        valueGaugeCoordinates 3
          (Ideal.absNorm
            (cyclotomicLinearFactorIdeal
              (cycloZeta_isPrimitiveRoot 3) 2 1)) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 3) (p := 3) (by norm_num)
    (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3)
  exact ⟨P, primeGauge_valueGaugeCoordinates_traceOne_eq_cyclotomicIdeal P 2 1 3⟩

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 3) 3
        (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3),
      valueGaugeCoordinates 3
          (Int.natAbs (norm (P.coord ((2 + 1 : ℕ) : ℤ) (1 : ℤ)))) =
        valueGaugeCoordinates 3 (GTail 3 1 2 1) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 3) (p := 3) (by norm_num)
    (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3)
  exact ⟨P,
    primeExponentGauge_valueGaugeCoordinates_traceOne_eq_GTail
      (primeExponentGauge_of_prime (by norm_num)) P 3⟩

/-! ## Prime-adic packet and fixed-prime calibrations -/

example {p g u x : ℕ} [Fact p.Prime]
    (P : PrimeAdicFactorPacket p g u x) :
    PrimeExponentGauge p :=
  P.exponentGauge

example (g u : ℕ) :
    PrimeExponentGauge 3 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (K := cycloField 3) (p := 3)
          (cycloZeta_isPrimitiveRoot 3) g u) : ℤ) =
        norm (⟨((g + u : ℕ) : ℤ), (u : ℤ)⟩ : TraceOneInt (-1)) :=
  primeExponentGauge_three_calibration (cycloZeta_isPrimitiveRoot 3) g u

example (g u : ℕ) :
    PrimeExponentGauge 5 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (K := cycloField 5) (p := 5)
          (cycloZeta_isPrimitiveRoot 5) g u) : ℤ) =
        norm
          (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
            (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) :=
  primeExponentGauge_five_calibration (cycloZeta_isPrimitiveRoot 5) g u

example (g u : ℕ) :
    PrimeExponentGauge 7 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal
          (K := cycloField 7) (p := 7)
          (cycloZeta_isPrimitiveRoot 7) g u) : ℤ) =
        norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne
          ((g + u : ℕ) : ℤ) (u : ℤ)) :=
  primeExponentGauge_seven_calibration (cycloZeta_isPrimitiveRoot 7) g u

end

end DkMathTest.FLT.Prime
