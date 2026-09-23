/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.PrimeCyclotomicCalibration

#print "file: DkMathTest.FLT.Prime.PrimeCyclotomicCalibration"

namespace DkMathTest.FLT.Prime

open DkMath.CFBRC
open DkMath.FLT.Prime
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Signed-parameter and p = 3 carrier calibration -/

example : signedPrimeParameter 3 = -1 := signedPrimeParameter_three

example : signedPrimeParameter 5 = 1 := signedPrimeParameter_five

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example :
    TraceOneInt (signedPrimeParameter 3) = TraceOneInt (-1) :=
  DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type

example (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 3) (p := 3) (cycloZeta_isPrimitiveRoot 3) g u) : ℤ) =
      norm (⟨((g + u : ℕ) : ℤ), (u : ℤ)⟩ : TraceOneInt (-1)) :=
  cyclotomicIdeal_absNorm_eq_traceOneNorm_three
    (cycloZeta_isPrimitiveRoot 3) g u

example :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 3) (p := 3) (cycloZeta_isPrimitiveRoot 3) 0 0) : ℤ) =
      norm (⟨(0 : ℤ), (0 : ℤ)⟩ : TraceOneInt (-1)) :=
  cyclotomicIdeal_absNorm_eq_traceOneNorm_three
    (cycloZeta_isPrimitiveRoot 3) 0 0

/-! ## p = 5 Golden/square-link calibration -/

example (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 5) (p := 5) (cycloZeta_isPrimitiveRoot 5) g u) : ℤ) =
      norm
        (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
          (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) :=
  cyclotomicIdeal_absNorm_eq_traceOneNorm_five
    (cycloZeta_isPrimitiveRoot 5) g u

example :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 5) (p := 5) (cycloZeta_isPrimitiveRoot 5) 0 0) : ℤ) =
      DkMath.FLT.Five.GoldenNorm 0 0 :=
  cyclotomicIdeal_absNorm_eq_goldenNorm_squareLink
    (cycloZeta_isPrimitiveRoot 5) 0 0

/-! ## p = 7 explicit cubic calibration -/

example (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 7) (p := 7) (cycloZeta_isPrimitiveRoot 7) g u) : ℤ) =
      norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne
        ((g + u : ℕ) : ℤ) (u : ℤ)) :=
  cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
    (cycloZeta_isPrimitiveRoot 7) g u

example :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal
        (K := cycloField 7) (p := 7) (cycloZeta_isPrimitiveRoot 7) 0 0) : ℤ) =
      norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne 0 0) :=
  cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
    (cycloZeta_isPrimitiveRoot 7) 0 0

/-! ## Generic packet to dedicated scalar calibration -/

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 3) 3
        (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3),
      norm (P.coord ((2 + 1 : ℕ) : ℤ) (1 : ℤ)) =
        norm (⟨(3 : ℤ), (1 : ℤ)⟩ : TraceOneInt (-1)) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 3) (p := 3) (by norm_num)
    (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3)
  exact ⟨P, coord_norm_eq_traceOneNorm_three P 2 1⟩

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 5) 5
        (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5),
      norm (P.coord ((1 + 0 : ℕ) : ℤ) (0 : ℤ)) =
        norm (⟨(1 : ℤ), (0 : ℤ)⟩ : TraceOneInt 1) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 5) (p := 5) (by norm_num)
    (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5)
  exact ⟨P, coord_norm_eq_traceOneNorm_five P 1 0⟩

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 7) 7
        (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7),
      norm (P.coord ((3 + 2 : ℕ) : ℤ) (2 : ℤ)) =
        norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne 5 2) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 7) (p := 7) (by norm_num)
    (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7)
  exact ⟨P, coord_norm_eq_traceOneNorm_seven P 3 2⟩

/-! ## Public theorem axiom audit -/

#print axioms DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_three
#print axioms DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_five
#print axioms DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_goldenNorm_squareLink
#print axioms DkMath.FLT.Prime.cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
#print axioms DkMath.FLT.Prime.coord_norm_eq_traceOneNorm_three
#print axioms DkMath.FLT.Prime.coord_norm_eq_traceOneNorm_five
#print axioms DkMath.FLT.Prime.coord_norm_eq_traceOneNorm_seven

end

end DkMathTest.FLT.Prime
