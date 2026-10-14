/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
import DkMath.FLT.Seven.SeventhPowerCoordinates
import DkMath.NumberTheory.TraceOnePrimeDiscriminant
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import Mathlib.Tactic

#print "file: DkMath.FLT.Seven.PrimeTraceOneClosureBridge"

namespace DkMath.FLT.Seven

open DkMath.FLT.Prime
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge

noncomputable section

/-! ## Neutral recurrence to explicit seventh-power coordinates -/

theorem traceOnePowCoords_negTwo_seven_fst (u v : ℤ) :
    (traceOnePowCoords (-2) u v 7).1 = seventhPowerFst u v := by
  have hrec := traceOne_pow_coordinates (-2) u v 7
  have hexp := traceOne_pow_seven_eq u v
  exact (congrArg TraceOneInt.fst hrec).symm.trans
    (congrArg TraceOneInt.fst hexp)

theorem traceOnePowCoords_negTwo_seven_snd (u v : ℤ) :
    (traceOnePowCoords (-2) u v 7).2 = seventhPowerSnd u v := by
  have hrec := traceOne_pow_coordinates (-2) u v 7
  have hexp := traceOne_pow_seven_eq u v
  exact (congrArg TraceOneInt.snd hrec).symm.trans
    (congrArg TraceOneInt.snd hexp)

/-! ## Residual terminality and the p=7 unit norm -/

theorem not_seven_dvd_natAbs_norm_of_primeTraceOne_residual_axis_terminal
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ¬ 7 ∣ Int.natAbs (norm Q.residual) := by
  let DP : PrimeDiscriminantPacket 7 (signedPrimeParameter 7) :=
    signedPrimeDiscriminantPacket (by norm_num) (by norm_num)
  intro hnorm
  apply Q.residual_axis_terminal
  exact (DP.discrAxis_dvd_iff_prime_dvd_natAbs_norm Q.residual).mpr hnorm

theorem not_seven_dvd_norm_of_primeTraceOne_residual_axis_terminal
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ¬ (7 : ℤ) ∣ norm Q.residual := by
  intro hnorm
  exact not_seven_dvd_natAbs_norm_of_primeTraceOne_residual_axis_terminal
    P0 P Q ((Int.natCast_dvd).mp hnorm)

/-! ## Explicit residual coordinates -/

theorem exists_seventhPowerCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ u v : ℤ,
      Q.residual.fst = seventhPowerFst u v ∧
      Q.residual.snd = seventhPowerSnd u v := by
  rcases exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
      P0 P Q with ⟨u, v, hfst, hsnd⟩
  refine ⟨u, v, hfst.trans ?_, hsnd.trans ?_⟩
  · simpa [signedPrimeParameter, signedPrimeDiscriminant] using
      traceOnePowCoords_negTwo_seven_fst u v
  · simpa [signedPrimeParameter, signedPrimeDiscriminant] using
      traceOnePowCoords_negTwo_seven_snd u v

/-! ## Same-root seventh-power endpoint -/

theorem exists_seventhPowerRoot_not_seven_dvd_norm_of_primeTraceOnePacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ delta : TraceOneInt (signedPrimeParameter 7),
      Q.residual = delta ^ 7 ∧
      ¬ (7 : ℤ) ∣ norm delta := by
  have hexact :=
    exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
      P0 P Q
  rcases hexact with ⟨delta, hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro hdeltaNorm
  apply not_seven_dvd_norm_of_primeTraceOne_residual_axis_terminal P0 P Q
  rw [hdelta]
  rw [traceOne_norm_pow]
  exact dvd_pow hdeltaNorm (by norm_num : 7 ≠ 0)

theorem exists_seventhPowerCoords_and_root_not_seven_dvd_norm_of_primeTraceOnePacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ u v : ℤ,
      Q.residual.fst = seventhPowerFst u v ∧
      Q.residual.snd = seventhPowerSnd u v ∧
      ¬ (7 : ℤ) ∣ norm (⟨u, v⟩ : TraceOneInt (signedPrimeParameter 7)) := by
  rcases exists_seventhPowerRoot_not_seven_dvd_norm_of_primeTraceOnePacket
      P0 P Q with ⟨delta, hdelta, hnorm⟩
  rcases delta with ⟨u, v⟩
  refine ⟨u, v, ?_, ?_, hnorm⟩
  · have hcoord := congrArg TraceOneInt.fst hdelta
    have hpow := traceOne_pow_coordinates (signedPrimeParameter 7) u v 7
    calc
      Q.residual.fst = ((⟨u, v⟩ : TraceOneInt (signedPrimeParameter 7)) ^ 7).fst := hcoord
      _ = (traceOnePowCoords (signedPrimeParameter 7) u v 7).1 :=
        congrArg TraceOneInt.fst hpow
      _ = seventhPowerFst u v := by
        simpa [signedPrimeParameter, signedPrimeDiscriminant] using
          traceOnePowCoords_negTwo_seven_fst u v
  · have hcoord := congrArg TraceOneInt.snd hdelta
    have hpow := traceOne_pow_coordinates (signedPrimeParameter 7) u v 7
    calc
      Q.residual.snd = ((⟨u, v⟩ : TraceOneInt (signedPrimeParameter 7)) ^ 7).snd := hcoord
      _ = (traceOnePowCoords (signedPrimeParameter 7) u v 7).2 :=
        congrArg TraceOneInt.snd hpow
      _ = seventhPowerSnd u v := by
        simpa [signedPrimeParameter, signedPrimeDiscriminant] using
          traceOnePowCoords_negTwo_seven_snd u v

/-! ## Direct p=7 coordinate consequences -/

theorem exists_seventhPowerCoords_residual_snd_dvd_seven_of_primeTraceOnePacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ u v : ℤ,
      Q.residual.fst = seventhPowerFst u v ∧
      Q.residual.snd = seventhPowerSnd u v ∧
      (7 : ℤ) ∣ Q.residual.snd := by
  rcases exists_seventhPowerCoords_and_root_not_seven_dvd_norm_of_primeTraceOnePacket
      P0 P Q with ⟨u, v, hfst, hsnd, hnorm⟩
  refine ⟨u, v, hfst, hsnd, ?_⟩
  rw [hsnd, seventhPowerSnd_eq_seven_mul]
  refine ⟨v * seventhPowerSndCore u v, ?_⟩
  ring

theorem exists_seventhPowerCoords_residual_sndCore_not_dvd_seven_of_primeTraceOnePacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ u v : ℤ,
      Q.residual.fst = seventhPowerFst u v ∧
      Q.residual.snd = seventhPowerSnd u v ∧
      ¬ (7 : ℤ) ∣ seventhPowerSndCore u v := by
  rcases exists_seventhPowerCoords_and_root_not_seven_dvd_norm_of_primeTraceOnePacket
      P0 P Q with ⟨u, v, hfst, hsnd, hnorm⟩
  refine ⟨u, v, hfst, hsnd, ?_⟩
  exact seven_not_dvd_seventhPowerSndCore_of_norm hnorm

theorem exists_seventhPowerCoords_residual_snd_fortyNine_iff_dvd_seven_of_primeTraceOnePacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ u v : ℤ,
      Q.residual.fst = seventhPowerFst u v ∧
      Q.residual.snd = seventhPowerSnd u v ∧
      ((49 : ℤ) ∣ Q.residual.snd ↔ (7 : ℤ) ∣ v) := by
  rcases exists_seventhPowerCoords_and_root_not_seven_dvd_norm_of_primeTraceOnePacket
      P0 P Q with ⟨u, v, hfst, hsnd, hnorm⟩
  refine ⟨u, v, hfst, hsnd, ?_⟩
  simpa [hsnd] using fortyNine_dvd_seventhPowerSnd_iff hnorm

end

end DkMath.FLT.Seven
