/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneConjugateCoprime
import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.FLT.Seven.AxisDivisibility
import DkMath.FLT.Seven.PrimitiveCoordinateCoprime

#print "file: DkMathTest.FLT.Prime.TraceOneConjugateCoprimeProbe"

open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open DkMath.FLT.Seven

namespace DkMathTest.FLT.Prime.TraceOneConjugateCoprimeProbe

/-! p=3: the generic carrier theorem is available at the first odd prime. -/

example {w : TraceOneInt (signedPrimeParameter 3)}
    (hcoords : IsCoprime w.fst w.snd)
    (hterminal : ¬ discrAxis (signedPrimeParameter 3) ∣ w) :
    IsCoprime (Ideal.span ({w} : Set (TraceOneInt (signedPrimeParameter 3))))
      (Ideal.span ({conj w} : Set (TraceOneInt (signedPrimeParameter 3)))) := by
  letI : Field (TraceOneRat (signedPrimeParameter 3)) :=
    traceOneRatField (p := 3) (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 3)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 3)) :=
    traceOneRat_isDedekindDomain (p := 3) (by norm_num) (by norm_num)
  let P : PrimeDiscriminantPacket 3 (signedPrimeParameter 3) :=
    { prime := by norm_num
      discr_natAbs := by
        norm_num [discr, signedPrimeParameter, signedPrimeDiscriminant] }
  exact ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
    P hcoords hterminal

/-! p=5: the common-divisor kernel is exercised in `TraceOneInt 1`. -/

example {w d : TraceOneInt (signedPrimeParameter 5)}
    (hcoords : IsCoprime w.fst w.snd)
    (hdw : d ∣ w) (hdconj : d ∣ conj w) :
    d ∣ discrAxis (signedPrimeParameter 5) := by
  exact common_divisor_dvd_discrAxis_of_coordinate_coprime
    hcoords hdw hdconj

example {x : TraceOneInt (signedPrimeParameter 5)} (hx : norm x ≠ 0)
    {c : ℕ} (hNorm : Int.natAbs (norm x) = 5 * c ^ 5)
    (hc : ¬ 5 ∣ c) :
    ∃ y : TraceOneInt (signedPrimeParameter 5),
      x = discrAxis (signedPrimeParameter 5) * y ∧
      norm y ≠ 0 ∧
      ¬ discrAxis (signedPrimeParameter 5) ∣ y ∧
      ∃ k : ℤ, norm y = k ^ 5 := by
  let P : PrimeDiscriminantPacket 5 (signedPrimeParameter 5) :=
    { prime := by norm_num
      discr_natAbs := by
        norm_num [discr, signedPrimeParameter, signedPrimeDiscriminant] }
  exact P.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
    hx hNorm hc

/-! p=7: the specialized cyclotomic coordinate package enters the generic
kernel, with the axis-terminal branch witnessed by the gap `2 - 1`. -/

example :
    let w : TraceOneInt (signedPrimeParameter 7) :=
      ⟨cyclotomicSevenFst (2 : ℤ) (1 : ℤ),
        cyclotomicSevenSnd (2 : ℤ) (1 : ℤ)⟩
    IsCoprime (Ideal.span ({w} : Set (TraceOneInt (signedPrimeParameter 7))))
      (Ideal.span ({conj w} : Set (TraceOneInt (signedPrimeParameter 7)))) := by
  letI : Field (TraceOneRat (signedPrimeParameter 7)) :=
    traceOneRatField (p := 7) (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 7)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 7)) :=
    traceOneRat_isDedekindDomain (p := 7) (by norm_num) (by norm_num)
  let P : PrimeDiscriminantPacket 7 (signedPrimeParameter 7) :=
    { prime := by norm_num
      discr_natAbs := by
        norm_num [discr, signedPrimeParameter, signedPrimeDiscriminant] }
  let w : TraceOneInt (signedPrimeParameter 7) :=
    ⟨cyclotomicSevenFst (2 : ℤ) (1 : ℤ),
      cyclotomicSevenSnd (2 : ℤ) (1 : ℤ)⟩
  have hcoords : IsCoprime w.fst w.snd := by
    simpa [w, cyclotomicSevenToTraceOne, signedPrimeParameter,
      signedPrimeDiscriminant] using
      (cyclotomicSeven_coordinates_isCoprime (z := 2) (y := 1) (by norm_num))
  have hterminal : ¬ discrAxis (signedPrimeParameter 7) ∣ w := by
    intro haxis
    have hp : 7 ∣ Int.natAbs (norm w) :=
      (P.discrAxis_dvd_iff_prime_dvd_natAbs_norm w).mp haxis
    norm_num [w, DkMath.NumberTheory.TraceOneQuadratic.norm,
      signedPrimeParameter, signedPrimeDiscriminant,
      cyclotomicSevenFst, cyclotomicSevenSnd] at hp
  have hcop := ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
    P hcoords hterminal
  exact hcop

/-! The remaining signed parameters exercise the generic prime-axis API on
the imaginary p=11 and real p=13 carriers. -/

example :
    Prime (discrAxis (signedPrimeParameter 11)) := by
  letI : Field (TraceOneRat (signedPrimeParameter 11)) :=
    traceOneRatField (p := 11) (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 11)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let P : PrimeDiscriminantPacket 11 (signedPrimeParameter 11) :=
    { prime := by norm_num
      discr_natAbs := by
        norm_num [discr, signedPrimeParameter, signedPrimeDiscriminant] }
  exact P.prime_discrAxis

example {w : TraceOneInt (signedPrimeParameter 13)}
    (hcoords : IsCoprime w.fst w.snd)
    (hterminal : ¬ discrAxis (signedPrimeParameter 13) ∣ w) :
    IsCoprime (Ideal.span ({w} : Set (TraceOneInt (signedPrimeParameter 13))))
      (Ideal.span ({conj w} : Set (TraceOneInt (signedPrimeParameter 13)))) := by
  letI : Field (TraceOneRat (signedPrimeParameter 13)) :=
    traceOneRatField (p := 13) (by norm_num) (by norm_num)
  letI : IsDomain (TraceOneInt (signedPrimeParameter 13)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter 13)) :=
    traceOneRat_isDedekindDomain (p := 13) (by norm_num) (by norm_num)
  let P : PrimeDiscriminantPacket 13 (signedPrimeParameter 13) :=
    { prime := by norm_num
      discr_natAbs := by
        norm_num [discr, signedPrimeParameter, signedPrimeDiscriminant] }
  exact ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
    P hcoords hterminal

end DkMathTest.FLT.Prime.TraceOneConjugateCoprimeProbe
