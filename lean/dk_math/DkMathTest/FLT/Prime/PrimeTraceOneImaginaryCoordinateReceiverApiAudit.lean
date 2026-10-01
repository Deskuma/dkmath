/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneImaginaryCoordinateReceiverApiAudit"

open DkMath.FLT.Prime
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

#check DkMath.Lib.NumberTheory.traceOnePowCoords
#check DkMath.Lib.NumberTheory.traceOne_pow_coordinates
#check DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff
#check DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
#check DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
#check DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegTwo_seven
#check DkMath.FLT.Prime.exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
#check DkMath.FLT.Prime.exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven

#synth CommRing (TraceOneInt 0)

example {s : ℤ} {alpha : TraceOneInt s} {r : ℕ} :
    (∃ gamma : TraceOneInt s, alpha = 1 * gamma ^ r) ↔
      ∃ m n : ℤ,
        alpha.fst = (traceOnePowCoords s m n r).1 ∧
          alpha.snd = (traceOnePowCoords s m n r).2 := by
  simpa [DkMath.NumberTheory.TraceOneQuadratic.conj,
      DkMath.NumberTheory.TraceOneQuadratic.norm] using
    (traceOne_pow_core_landing_iff
      (alpha := alpha) (beta := (1 : TraceOneInt s)) (r := r)
      (by simp [DkMath.NumberTheory.TraceOneQuadratic.norm]))

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : signedPrimeParameter 11 = -3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
    let : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField P0.prime (by omega)
    let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain P0.prime (by omega)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ m n : ℤ,
        Q.residual.fst =
            (traceOnePowCoords (signedPrimeParameter p) m n p).1 ∧
          Q.residual.snd =
            (traceOnePowCoords (signedPrimeParameter p) m n p).2 := by
  exact exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
    P0 P Q hp7 hmod

example {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ m n : ℤ,
      Q.residual.fst =
          (traceOnePowCoords (signedPrimeParameter 7) m n 7).1 ∧
        Q.residual.snd =
          (traceOnePowCoords (signedPrimeParameter 7) m n 7).2 := by
  exact exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    P0 P Q

example {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 11)]
    [IsCyclotomicExtension {11} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 11}
    (P0 : PrimeAdicFactorPacket 11 g u x)
    (P : PrimeTraceOneCoordinatePacket L 11 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 11 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root P0.prime (by norm_num)⟩
    let : Field (TraceOneRat (signedPrimeParameter 11)) :=
      traceOneRatField P0.prime (by norm_num)
    let : IsDomain (TraceOneInt (signedPrimeParameter 11)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter 11)) :=
      traceOneRat_isDedekindDomain P0.prime (by norm_num)
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter 11)) 11 →
      ∃ m n : ℤ,
        Q.residual.fst =
            (traceOnePowCoords (signedPrimeParameter 11) m n 11).1 ∧
          Q.residual.snd =
            (traceOnePowCoords (signedPrimeParameter 11) m n 11).2 := by
  exact exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
    P0 P Q (by norm_num) (by norm_num)
