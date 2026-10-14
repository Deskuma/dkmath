/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerFactor
import DkMath.FLT.Seven.QuadraticEuclidean
import DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.RingTheory.ClassGroup.Basic

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneClassGroupClosureApiAudit"

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

#check card_classGroup_eq_one
#check card_classGroup_eq_one_iff
#check Fintype.card_eq_one_iff
#check EuclideanDomain.instIsPrincipalIdealRing
#check classGroupPTorsionFreeAt
#check classGroup_eq_one_of_pow_eq_one_of_classGroupPTorsionFreeAt
#check ideal_isPrincipal_of_classGroup_eq_one
#check ideal_isPrincipal_of_classGroupPTorsionFreeAt
#check ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
#check exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check DkMath.FLT.Seven.traceOneNegTwoEuclideanDomain
#check DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegTwo_seven
#check DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven

#synth EuclideanDomain (TraceOneInt (-2))
#synth IsPrincipalIdealRing (TraceOneInt (-2))

example {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : Subsingleton (ClassGroup R) := by
  rcases Fintype.card_eq_one_iff.mp (card_classGroup_eq_one (R := R)) with ⟨x, hx⟩
  exact ⟨fun a b => (hx a).trans (hx b).symm⟩

example {R : Type*} [CommRing R] [IsDomain R] [Subsingleton (ClassGroup R)]
    (p : ℕ) : classGroupPTorsionFreeAt R p := by
  intro a _
  exact Subsingleton.elim _ _

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : classGroupPTorsionFreeAt (TraceOneInt (-2)) 7 := by
  let : Subsingleton (ClassGroup (TraceOneInt (-2))) := by
    rcases Fintype.card_eq_one_iff.mp
      (card_classGroup_eq_one (R := TraceOneInt (-2))) with ⟨x, hx⟩
    exact ⟨fun a b => (hx a).trans (hx b).symm⟩
  exact fun a _ => Subsingleton.elim _ _
