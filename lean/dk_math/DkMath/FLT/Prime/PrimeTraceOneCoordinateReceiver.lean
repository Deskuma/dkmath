/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
import DkMath.Lib.NumberTheory.TraceOnePowerLanding
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver"

namespace DkMath.FLT.Prime

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section

local notation "traceNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-! ## Generic imaginary residual coordinate receiver -/

/-- The generic imaginary exact-power endpoint in recurrence coordinates. -/
theorem exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
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
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root P0.prime (by omega)⟩
  let : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime (by omega)
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime (by omega)
  dsimp
  intro hfree
  obtain ⟨delta, hdelta⟩ :=
    exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
      P0 P Q hp7 hmod hfree
  have hone : traceNorm (1 : TraceOneInt (signedPrimeParameter p)) ≠ 0 := by
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  have hfactor :
      ∃ gamma : TraceOneInt (signedPrimeParameter p),
        Q.residual = 1 * gamma ^ p := by
    refine ⟨delta, ?_⟩
    simpa using hdelta
  obtain ⟨m, n, hfst, hsnd⟩ :=
    (traceOne_pow_core_landing_iff
      (alpha := Q.residual)
      (beta := (1 : TraceOneInt (signedPrimeParameter p)))
      (r := p) hone).mp hfactor
  refine ⟨m, n, ?_, ?_⟩
  · simpa [DkMath.NumberTheory.TraceOneQuadratic.conj,
      DkMath.NumberTheory.TraceOneQuadratic.norm] using hfst
  · simpa [DkMath.NumberTheory.TraceOneQuadratic.conj,
      DkMath.NumberTheory.TraceOneQuadratic.norm] using hsnd

/-! ## p=7 class-group-closed regression -/

/-- The p=7 structural endpoint in recurrence coordinates. -/
theorem exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    {L : Type*} [Field L] [Algebra ℚ L]
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
  have hgeneric :=
    exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
      P0 P Q (by norm_num) (by norm_num)
  dsimp at hgeneric
  exact hgeneric (by
    simpa [signedPrimeParameter, signedPrimeDiscriminant] using
      classGroupPTorsionFreeAt_traceOneNegTwo_seven)

end

end DkMath.FLT.Prime
