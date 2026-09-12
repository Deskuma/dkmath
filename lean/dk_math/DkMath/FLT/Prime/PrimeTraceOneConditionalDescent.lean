/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
import DkMath.Lib.NumberTheory.PrincipalIdealPower
import DkMath.Lib.NumberTheory.UnitPowerSector
import DkMath.NumberTheory.TraceOnePrimeUnitSectors
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneConditionalDescent"

namespace DkMath.FLT.Prime

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors

noncomputable section

/-! ## Branch-independent conditional endpoints -/

theorem exists_unit_mul_pow_of_primeTraceOneStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime hp2
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime hp2
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ u gamma : TraceOneInt (signedPrimeParameter p),
        IsUnit u ∧
        Ideal.span ({gamma} : Set (TraceOneInt (signedPrimeParameter p))) =
          Q.idealRoot ∧
        Q.residual = u * gamma ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime hp2
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime hp2
  intro hfree
  exact exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    Q.idealRoot_nonzero hfree Q.residual_span_eq

/-! A supplied neutral sector system composes with the same ideal-root packet;
the theorem is independent of whether the sectors are real, imaginary, or
provided by another carrier-specific construction. -/
theorem exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (S : UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p)
    (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime hp2
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime hp2
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ s : S.Sector, ∃ delta : TraceOneInt (signedPrimeParameter p),
        Q.residual = (S.rep s : TraceOneInt (signedPrimeParameter p)) *
          delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime hp2
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime hp2
  intro hfree
  exact exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    S Q.idealRoot_nonzero hfree Q.residual_span_eq

/-! ## Imaginary and real branch closures -/

theorem exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime (by omega)
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime (by omega)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ delta : TraceOneInt (signedPrimeParameter p),
        Q.residual = delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime (by omega)
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime (by omega)
  intro hfree
  exact traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
    P0.prime hp7 hmod Q.idealRoot_nonzero hfree Q.residual_span_eq

theorem exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hmod : p % 4 = 1) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime (by omega)
    letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime (by omega)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ i : Fin p, ∃ delta : TraceOneInt (signedPrimeParameter p),
        Q.residual =
          (traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i * delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime (by omega)
  letI : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime (by omega)
  intro hfree
  exact traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow
    P0.prime hmod Q.idealRoot_nonzero hfree Q.residual_span_eq

end

end DkMath.FLT.Prime
