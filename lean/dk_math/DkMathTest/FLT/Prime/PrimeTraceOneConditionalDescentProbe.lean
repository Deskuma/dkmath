/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.FLT.Seven.QuadraticResidualPacket
import DkMath.FLT.Three.EisensteinUnitSectors

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentProbe"

namespace DkMathTest.FLT.Prime

open DkMath.FLT.Seven
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.NumberTheory.TraceOnePrimeUnitSectors
open DkMath.FLT.Three

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

/-! p=3 is audited at its existing EisensteinInt carrier.  No TraceOneInt
equivalence or generic three-sector production adapter is asserted here. -/
example (u : EisensteinIntˣ) :
    ∃ sector : EisensteinUnitSector, ∃ delta : EisensteinInt,
      IsUnit delta ∧ (u : EisensteinInt) = sector.rep * delta ^ 3 :=
  exists_sector_mul_cube_of_unit u

/-! The p=7 specialized route retains the same exact-power shape, while the
generic conditional theorem below consumes the Phase-25 packet. -/
example {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    ∃ b : ℕ, norm q.residualCore = (b : ℤ) ^ 7 :=
  q.norm_is_seventh_power

example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 7 g u x) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 7 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 7)) :=
      traceOneRatField (by norm_num) (by norm_num)
    letI : IsDomain (TraceOneInt (signedPrimeParameter 7)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 7)) :=
      traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 7)) 7 → True := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 7 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
  letI : Field (TraceOneRat (signedPrimeParameter 7)) :=
    traceOneRatField (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 7)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 7)) :=
    traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
  intro hfree
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 7) (p := 7) (by norm_num)
    (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7)
  obtain ⟨Q⟩ := DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket P0 P
  have hdelta :=
    DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
      P0 P Q (by norm_num) (by norm_num) hfree
  trivial

example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 11 g u x) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 11 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 11)) :=
      traceOneRatField (by norm_num) (by norm_num)
    letI : IsDomain (TraceOneInt (signedPrimeParameter 11)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 11)) :=
      traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 11)) 11 → True := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 11 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
  letI : Field (TraceOneRat (signedPrimeParameter 11)) :=
    traceOneRatField (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 11)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 11)) :=
    traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
  intro hfree
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 11) (p := 11) (by norm_num)
    (cycloZeta 11) (cycloZeta_isPrimitiveRoot 11)
  obtain ⟨Q⟩ := DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket P0 P
  have hdelta :=
    DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
      P0 P Q (by norm_num) (by norm_num) hfree
  trivial

/-! The real p=5 and p=13 endpoints retain their finite sector. -/
example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 5 g u x) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 5)) :=
      traceOneRatField (by norm_num) (by norm_num)
    letI : NumberField (TraceOneRat (signedPrimeParameter 5)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    letI : IsDomain (TraceOneInt (signedPrimeParameter 5)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 5)) :=
      traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 5)) 5 → True := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 5 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
  letI : Field (TraceOneRat (signedPrimeParameter 5)) :=
    traceOneRatField (by norm_num) (by norm_num)
  letI : NumberField (TraceOneRat (signedPrimeParameter 5)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  letI : IsDomain (TraceOneInt (signedPrimeParameter 5)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 5)) :=
    traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
  intro hfree
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 5) (p := 5) (by norm_num)
    (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5)
  obtain ⟨Q⟩ := DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket P0 P
  have hsector :=
    DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
      P0 P Q (by norm_num) hfree
  trivial

example {g u x : ℕ}
    (P0 : DkMath.FLT.Prime.PrimeAdicFactorPacket 13 g u x) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 13 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
    letI : Field (TraceOneRat (signedPrimeParameter 13)) :=
      traceOneRatField (by norm_num) (by norm_num)
    letI : NumberField (TraceOneRat (signedPrimeParameter 13)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    letI : IsDomain (TraceOneInt (signedPrimeParameter 13)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 13)) :=
      traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 13)) 13 → True := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 13 : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root (by norm_num) (by norm_num)⟩
  letI : Field (TraceOneRat (signedPrimeParameter 13)) :=
    traceOneRatField (by norm_num) (by norm_num)
  letI : NumberField (TraceOneRat (signedPrimeParameter 13)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  letI : IsDomain (TraceOneInt (signedPrimeParameter 13)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 13)) :=
    traceOneRat_isDedekindDomain (by norm_num) (by norm_num)
  intro hfree
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 13) (p := 13) (by norm_num)
    (cycloZeta 13) (cycloZeta_isPrimitiveRoot 13)
  obtain ⟨Q⟩ := DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket P0 P
  have hsector :=
    DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
      P0 P Q (by norm_num) hfree
  trivial

end

end DkMathTest.FLT.Prime
