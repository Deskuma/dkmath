/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.FLT.Seven.QuadraticEuclidean
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ClassGroup.Basic

#print "file: DkMathTest.Lib.NumberTheory.ClassGroupTorsionCardinalityApiAudit"

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic

#check classGroupPTorsionFreeAt
#check classGroupPTorsionFreeAt_of_subsingleton_classGroup
#check classGroupPTorsionFreeAt_of_isPrincipalIdealRing
#check classGroupPTorsionFreeAt_of_coprime_card
#check ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
#check orderOf_dvd_of_pow_eq_one
#check orderOf_dvd_card
#check orderOf_eq_one_iff
#check Fintype.card
#check Nat.Coprime
#check Nat.Coprime.gcd_eq_one
#check Nat.eq_one_of_dvd_coprimes
#check FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime
#check Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime

#synth Fintype (ClassGroup (TraceOneInt (-2)))
#synth IsPrincipalIdealRing (TraceOneInt (-2))
#synth IsDedekindDomain (TraceOneInt (-2))

example {R : Type*} [CommRing R] [IsDomain R]
    [Fintype (ClassGroup R)] {p : ℕ}
    (hcop : Nat.Coprime p (Fintype.card (ClassGroup R))) :
    classGroupPTorsionFreeAt R p := by
  intro a hpow
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hpow) orderOf_dvd_card

example {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (p : ℕ) :
    classGroupPTorsionFreeAt R p := by
  exact classGroupPTorsionFreeAt_of_isPrincipalIdealRing p

example : Nat.Coprime 7
    (Fintype.card (ClassGroup (TraceOneInt (-2)))) := by
  rw [card_classGroup_eq_one]
  norm_num

example : classGroupPTorsionFreeAt
    (TraceOneInt (-2)) 7 := by
  apply classGroupPTorsionFreeAt_of_coprime_card
  rw [card_classGroup_eq_one]
  norm_num

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Fintype (ClassGroup R)] {I : Ideal R} {p : ℕ}
    (hcop : Nat.Coprime p (Fintype.card (ClassGroup R)))
    (hI : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  exact Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hcop hI
