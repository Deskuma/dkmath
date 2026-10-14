/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticEuclidean
import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.NumberTheory.PrimeQuadraticDiscriminant

#print "file: DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure"

namespace DkMath.FLT.Prime

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

/-! The p=7 carrier is definitionally the Euclidean `TraceOneInt (-2)` order. -/
theorem classGroupPTorsionFreeAt_traceOneNegTwo_seven :
    classGroupPTorsionFreeAt (TraceOneInt (-2)) 7 :=
  classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7

/-! The generic imaginary endpoint, specialized only by the structural
class-group discharge.  This is not the specialized FLT7 contradiction. -/
theorem exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    let : IsDomain (TraceOneInt (signedPrimeParameter 7)) := by
      rw [show signedPrimeParameter 7 = -2 by
        norm_num [signedPrimeParameter, signedPrimeDiscriminant]]
      infer_instance
    ∃ delta : TraceOneInt (signedPrimeParameter 7),
      Q.residual = delta ^ 7 := by
  dsimp
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter 7 : ℚ) + 1 * r) := by
    exact ⟨traceOneRat_no_rational_root Nat.prime_seven (by norm_num)⟩
  let : Field (TraceOneRat (signedPrimeParameter 7)) :=
    traceOneRatField Nat.prime_seven (by norm_num)
  have hgeneric :=
    exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
      P0 P Q (by norm_num) (by norm_num)
  dsimp at hgeneric
  apply hgeneric
  simpa [signedPrimeParameter, signedPrimeDiscriminant] using
    classGroupPTorsionFreeAt_traceOneNegTwo_seven

end DkMath.FLT.Prime
