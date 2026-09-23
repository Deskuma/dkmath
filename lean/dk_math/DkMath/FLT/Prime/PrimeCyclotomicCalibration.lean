/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.TraceOneBridge
import DkMath.FLT.Prime.PrimeCyclotomicTraceOne
import DkMath.FLT.Seven.QuadraticBridge
import DkMath.FLT.Three.EisensteinLibBridge
import DkMath.FLT.ThreeTraceOneBridge
import DkMath.NumberTheory.StructuralArithmetic.GNBridge

#print "file: DkMath.FLT.Prime.PrimeCyclotomicCalibration"

/-!
# Dedicated p = 3, 5, 7 calibration of the cyclotomic norm bridge

This module compares only scalar norm values.  It does not identify the
generic TraceOne coordinate packet with any dedicated fixed-prime element.
-/

namespace DkMath.FLT.Prime

open DkMath.CFBRC
open DkMath.FLT
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Dedicated ideal-norm calibrations -/

/-- The generic p = 3 ideal norm is the established `TraceOneInt (-1)` norm. -/
theorem cyclotomicIdeal_absNorm_eq_traceOneNorm_three
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal (K := K) (p := 3) hζ g u) : ℤ) =
      norm (⟨((g + u : ℕ) : ℤ), (u : ℤ)⟩ : TraceOneInt (-1)) := by
  rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]
  simpa using
    (DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
      (g + u) u (by omega))

/-- The generic p = 5 ideal norm is the Golden/square-link norm. -/
theorem cyclotomicIdeal_absNorm_eq_traceOneNorm_five
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal (K := K) (p := 5) hζ g u) : ℤ) =
      norm
        (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
          (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) := by
  calc
    (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := K) (p := 5) hζ g u) : ℤ) =
        ((DkMath.CosmicFormulaBinom.GN 5 g u : ℕ) : ℤ) := by
          rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]
    _ = (DkMath.FLT.Five.GN5 g u : ℤ) := by
          rw [GN5_eq_generic_GN]
    _ = norm
        (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
          (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) :=
      DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink g u

/-- The p = 5 calibration is also available through `GoldenNorm`. -/
theorem cyclotomicIdeal_absNorm_eq_goldenNorm_squareLink
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal (K := K) (p := 5) hζ g u) : ℤ) =
      DkMath.FLT.Five.GoldenNorm
        (((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ)
        (((g + u) * u : ℕ) : ℤ) := by
  calc
    (Ideal.absNorm
        (cyclotomicLinearFactorIdeal (K := K) (p := 5) hζ g u) : ℤ) =
        ((DkMath.CosmicFormulaBinom.GN 5 g u : ℕ) : ℤ) := by
          rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]
    _ = (DkMath.FLT.Five.GN5 g u : ℤ) := by
          rw [GN5_eq_generic_GN]
    _ = DkMath.FLT.Five.GoldenNorm
        (((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ)
        (((g + u) * u : ℕ) : ℤ) :=
      DkMath.FLT.Five.GN5_eq_goldenNorm_squareLink g u

/-- The generic p = 7 ideal norm is the explicit cubic TraceOne norm. -/
theorem cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {7} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 7) (g u : ℕ) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal (K := K) (p := 7) hζ g u) : ℤ) =
      norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne
        ((g + u : ℕ) : ℤ) (u : ℤ)) := by
  rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]
  simpa using
    (DkMath.FLT.Seven.GN_seven_sub_eq_traceOneNorm_negTwo
      (g + u) u (by omega))

/-! ## Generic packet calibrations -/

/-- A generic p = 3 TraceOne packet has the dedicated p = 3 norm. -/
theorem coord_norm_eq_traceOneNorm_three
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ 3}
    (P : PrimeTraceOneCoordinatePacket K 3 ζ hζ) (g u : ℕ) :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      norm (⟨((g + u : ℕ) : ℤ), (u : ℤ)⟩ : TraceOneInt (-1)) :=
  (TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u).trans
    (cyclotomicIdeal_absNorm_eq_traceOneNorm_three hζ g u)

/-- A generic p = 5 TraceOne packet has the dedicated p = 5 norm. -/
theorem coord_norm_eq_traceOneNorm_five
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ 5}
    (P : PrimeTraceOneCoordinatePacket K 5 ζ hζ) (g u : ℕ) :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      norm
        (⟨(((g + u) ^ 2 + u ^ 2 : ℕ) : ℤ),
          (((g + u) * u : ℕ) : ℤ)⟩ : TraceOneInt 1) :=
  (TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u).trans
    (cyclotomicIdeal_absNorm_eq_traceOneNorm_five hζ g u)

/-- A generic p = 7 TraceOne packet has the dedicated p = 7 norm. -/
theorem coord_norm_eq_traceOneNorm_seven
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {7} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ 7}
    (P : PrimeTraceOneCoordinatePacket K 7 ζ hζ) (g u : ℕ) :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      norm (DkMath.FLT.Seven.cyclotomicSevenToTraceOne
        ((g + u : ℕ) : ℤ) (u : ℤ)) :=
  (TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P g u).trans
    (cyclotomicIdeal_absNorm_eq_traceOneNorm_seven hζ g u)

end

end DkMath.FLT.Prime
