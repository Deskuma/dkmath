/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge
import DkMath.Lib.Cosmic.GTailCyclotomic
import DkMath.FLT.Prime.PrimeCyclotomicIdeal
import DkMath.FLT.Prime.PrimeCyclotomicTraceOne
import DkMath.FLT.Prime.PrimeCyclotomicCalibration

#print "file: DkMath.FLT.Prime.PrimeGaugeBridge"

/-!
# Exponent-gauge bridge to the prime cyclotomic carrier

This module exposes the semantic entry point from the Pascal exponent gauge to
the existing cyclotomic, ideal-norm, and TraceOne scalar chain.  It does not
re-prove any norm or ideal identity and it does not identify the carrier
objects themselves.
-/

namespace DkMath.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.NumberTheory.Gauge
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

/-! ## Exponent-gauge primality and homogeneous evaluation -/

/-- The prime stored in a prime-row exponent gauge. -/
theorem PrimeExponentGauge.prime
    {p : ℕ} (h : DkMath.NumberTheory.Gauge.PrimeExponentGauge p) :
    p.Prime :=
  DkMath.NumberTheory.innerRowSupportPrime_prime h

/-- A prime exponent gauge selects the homogeneous prime cyclotomic evaluation. -/
theorem primeExponentGauge_GTail_eq_cyclotomicHomEval
    {R : Type*} [CommRing R] {p : ℕ}
    (hGauge : DkMath.NumberTheory.Gauge.PrimeExponentGauge p)
    (x u : R) :
    DkMath.CosmicFormula.GTail p 1 x u =
      DkMath.CosmicFormula.GTailCyclotomicHomEval
        p (Polynomial.cyclotomic p ℤ) x u := by
  have hp : p.Prime := PrimeExponentGauge.prime hGauge
  calc
    DkMath.CosmicFormula.GTail p 1 x u =
        DkMath.CosmicFormula.GTailCyclotomicShell p x u :=
      DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell p x u
    _ = DkMath.CosmicFormula.GTailCyclotomicHomEval
        p (Polynomial.cyclotomic p ℤ) x u :=
      (DkMath.CosmicFormula.GTailCyclotomicHomEval_prime_eq_shell hp x u).symm

/-! ## Exponent-gauge ideal resolution -/

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The cyclotomic principal-ideal norm resolves to the same `GTail` scalar. -/
theorem primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K}
    (hGauge : DkMath.NumberTheory.Gauge.PrimeExponentGauge p)
    (hζ : IsPrimitiveRoot ζ p) :
    Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) =
      DkMath.CosmicFormula.GTail p 1 g u := by
  let hFact : Fact p.Prime := ⟨PrimeExponentGauge.prime hGauge⟩
  simpa [DkMath.CosmicFormulaBinom.GN] using
    (@cyclotomicLinearFactorIdeal_absNorm_eq_GN
      K _ _ _ p g u hFact _ ζ hζ)

/-! ## ValueGauge conservation -/

/-- Resolving the ideal carrier preserves every ValueGauge coordinate. -/
theorem primeExponentGauge_valueGaugeCoordinates_cyclotomicIdeal_eq_GTail
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hGauge : DkMath.NumberTheory.Gauge.PrimeExponentGauge p)
    (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    valueGaugeCoordinates n
        (Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u)) =
      valueGaugeCoordinates n (DkMath.CosmicFormula.GTail p 1 g u) := by
  rw [primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail hGauge hζ]

/-! ## Prime-adic packet integration -/

/-- A prime-adic factor packet supplies its exponent-side gauge. -/
theorem PrimeAdicFactorPacket.exponentGauge
    {p g u x : ℕ} (P : PrimeAdicFactorPacket p g u x) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge p :=
  DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime P.prime

/-- The packet combines exponent gauge data with the existing ideal equation. -/
theorem PrimeAdicFactorPacket.gauge_resolves_to_cyclotomicIdeal
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : PrimeAdicFactorPacket p g u x) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge p ∧
      g * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) = x ^ p := by
  exact ⟨P.exponentGauge, P.gap_mul_cyclotomicIdeal_absNorm_eq_pow hζ⟩

/-! ## TraceOne scalar conservation -/

/-- The TraceOne scalar norm and the ideal norm have identical ValueGauge data. -/
theorem primeGauge_valueGaugeCoordinates_traceOne_eq_cyclotomicIdeal
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u n : ℕ) :
    valueGaugeCoordinates n
        (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) =
      valueGaugeCoordinates n
        (Ideal.absNorm (cyclotomicLinearFactorIdeal (K := L) hζ g u)) := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]

/-- A TraceOne scalar norm reaches the same `GTail` ValueGauge coordinates. -/
theorem primeExponentGauge_valueGaugeCoordinates_traceOne_eq_GTail
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p g u : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (hGauge : DkMath.NumberTheory.Gauge.PrimeExponentGauge p)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (n : ℕ) :
    valueGaugeCoordinates n
        (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) =
      valueGaugeCoordinates n (DkMath.CosmicFormula.GTail p 1 g u) := by
  exact
    (primeGauge_valueGaugeCoordinates_traceOne_eq_cyclotomicIdeal P g u n).trans
      (primeExponentGauge_valueGaugeCoordinates_cyclotomicIdeal_eq_GTail
        hGauge hζ n)

/-! ## Fixed-prime scalar calibrations -/

/-- The p = 3 exponent gauge pairs with the established TraceOne scalar norm. -/
theorem primeExponentGauge_three_calibration
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (g u : ℕ) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge 3 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := K) (p := 3) hζ g u) : ℤ) =
        norm (⟨((g + u : ℕ) : ℤ), (u : ℤ)⟩ : TraceOneInt (-1)) := by
  exact ⟨DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime (by norm_num),
    cyclotomicIdeal_absNorm_eq_traceOneNorm_three hζ g u⟩

/-- The p = 5 exponent gauge pairs with the established TraceOne scalar norm. -/
theorem primeExponentGauge_five_calibration
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (g u : ℕ) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge 5 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := K) (p := 5) hζ g u) : ℤ) =
        norm
          (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
            (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) := by
  exact ⟨DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime (by norm_num),
    cyclotomicIdeal_absNorm_eq_traceOneNorm_five hζ g u⟩

/-- The p = 7 exponent gauge pairs with the established TraceOne scalar norm. -/
theorem primeExponentGauge_seven_calibration
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {7} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 7) (g u : ℕ) :
    DkMath.NumberTheory.Gauge.PrimeExponentGauge 7 ∧
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := K) (p := 7) hζ g u) : ℤ) =
        norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne
          ((g + u : ℕ) : ℤ) (u : ℤ)) := by
  exact ⟨DkMath.NumberTheory.Gauge.primeExponentGauge_of_prime (by norm_num),
    cyclotomicIdeal_absNorm_eq_traceOneNorm_seven hζ g u⟩

end

end DkMath.FLT.Prime

#print axioms DkMath.FLT.Prime.PrimeExponentGauge.prime
#print axioms DkMath.FLT.Prime.primeExponentGauge_GTail_eq_cyclotomicHomEval
#print axioms DkMath.FLT.Prime.primeExponentGauge_cyclotomicIdeal_absNorm_eq_GTail
#print axioms DkMath.FLT.Prime.primeExponentGauge_valueGaugeCoordinates_cyclotomicIdeal_eq_GTail
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.exponentGauge
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.gauge_resolves_to_cyclotomicIdeal
#print axioms DkMath.FLT.Prime.primeGauge_valueGaugeCoordinates_traceOne_eq_cyclotomicIdeal
#print axioms DkMath.FLT.Prime.primeExponentGauge_valueGaugeCoordinates_traceOne_eq_GTail
#print axioms DkMath.FLT.Prime.primeExponentGauge_three_calibration
#print axioms DkMath.FLT.Prime.primeExponentGauge_five_calibration
#print axioms DkMath.FLT.Prime.primeExponentGauge_seven_calibration
