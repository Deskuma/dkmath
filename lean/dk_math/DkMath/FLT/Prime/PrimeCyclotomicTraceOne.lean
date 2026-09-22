/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.CyclotomicIdeal
import DkMath.FLT.Prime.AdicPowerSplit
import DkMath.FLT.Prime.PrimeCyclotomicIdeal
import DkMath.NumberTheory.CyclotomicQRTraceOneBridge

#print "file: DkMath.FLT.Prime.PrimeCyclotomicTraceOne"

/-!
# Scalar compatibility of the cyclotomic ideal and TraceOne carriers

This module transports only the common scalar norm value.  It does not identify
the cyclotomic element or ideal with the TraceOne coordinate ring.
-/

namespace DkMath.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

/-! ## Generic TraceOne coordinate compatibility -/

namespace TraceOneScalar

/-- The TraceOne coordinate norm is the cast of the canonical ideal norm. -/
theorem coord_norm_eq_cyclotomicIdeal_absNorm
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u : ℕ) :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := L) (p := p) hζ g u) : ℤ) := by
  rw [P.coord_norm_eq]
  have hsub : ((g + u : ℕ) : ℤ) - (u : ℤ) = (g : ℤ) := by omega
  rw [hsub, ← DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell]
  rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]

/-- The nonnegative TraceOne norm is the canonical ideal absolute norm. -/
theorem coord_natAbs_norm_eq_cyclotomicIdeal_absNorm
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u : ℕ) :
    Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) =
      Ideal.absNorm (cyclotomicLinearFactorIdeal (K := L) (p := p) hζ g u) := by
  rw [TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u]
  simp

/-- Rational-prime valuation is unchanged across the two scalar carriers. -/
theorem padicValNat_coord_natAbs_norm_eq_ideal_absNorm
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p q : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u : ℕ) :
    padicValNat q (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) =
      padicValNat q
        (Ideal.absNorm (cyclotomicLinearFactorIdeal (K := L) (p := p) hζ g u)) := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]

/-- Rational-prime divisibility is unchanged across the two scalar carriers. -/
theorem dvd_coord_natAbs_norm_iff_dvd_ideal_absNorm
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p q : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (g u : ℕ) :
    q ∣ Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) ↔
      q ∣ Ideal.absNorm (cyclotomicLinearFactorIdeal (K := L) (p := p) hζ g u) := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]

end TraceOneScalar

/-! ## Prime-adic packet specialization -/

/-- A prime-adic packet has the same TraceOne and ideal scalar norm. -/
theorem PrimeAdicFactorPacket.coord_norm_eq_cyclotomicIdeal_absNorm
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (_P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := L) (p := p) hζ g u) : ℤ) :=
  TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u

/-- The complete packet equation through the TraceOne scalar norm. -/
theorem PrimeAdicFactorPacket.gap_mul_coord_natAbs_norm_eq_pow
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    g * Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) = x ^ p := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]
  exact P0.gap_mul_cyclotomicIdeal_absNorm_eq_pow hζ

/-! ## Ramified power split specialization -/

/-- The ramified ideal-norm normal form through the TraceOne scalar norm. -/
theorem PrimeAdicPowerSplit.coord_natAbs_norm_eq_prime_mul_pow
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (S : PrimeAdicPowerSplit p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) = p * S.b ^ p := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]
  exact S.cyclotomicIdeal_absNorm_eq_prime_mul_pow hζ

/-- The ramified prime valuation is transported to the TraceOne scalar. -/
theorem PrimeAdicPowerSplit.padicValNat_coord_natAbs_norm_eq_one
    {L : Type*} [Field L] [NumberField L] [CharZero L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (S : PrimeAdicPowerSplit p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    padicValNat p (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) = 1 := by
  rw [TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u]
  exact S.input.padicValNat_cyclotomicIdeal_absNorm_eq_one hζ

end

end DkMath.FLT.Prime
