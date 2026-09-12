/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
import DkMath.NumberTheory.TraceOneConjugateCoprime
import DkMath.NumberTheory.TraceOneIdealPower
import DkMath.NumberTheory.TraceOnePrimeDiscriminant
import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.Lib.NumberTheory.IdealPowerFactor
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal"

namespace DkMath.FLT.Prime

open scoped nonZeroDivisors

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

noncomputable section

/-! ## The Phase-25 packet -/

/-- The axis-stripped TraceOne residual and its ideal `p`-th power witness.

The packet is conditional on the existing arithmetic and cyclotomic inputs;
it deliberately stops before principalization or any class-group assertion.
-/
structure PrimeTraceOneStrippedIdealPacket
    (L : Type*) [Field L] [Algebra ℚ L]
    {p g u : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) : Type where
  adicSplit : PrimeAdicPowerSplit p g u x
  parent : TraceOneInt (signedPrimeParameter p)
  residual : TraceOneInt (signedPrimeParameter p)
  axis_eq : parent = discrAxis (signedPrimeParameter p) * residual
  parent_coordinate_coprime : IsCoprime parent.fst parent.snd
  residual_coordinate_coprime : IsCoprime residual.fst residual.snd
  residual_norm_ne_zero : norm residual ≠ 0
  residual_axis_terminal :
    ¬ discrAxis (signedPrimeParameter p) ∣ residual
  residual_norm_pow : ∃ k : ℤ, norm residual = k ^ p
  residual_conj_ideal_coprime :
    IsCoprime (Ideal.span ({residual} : Set _))
      (Ideal.span ({conj residual} : Set _))
  idealRoot : Ideal (TraceOneInt (signedPrimeParameter p))
  idealRoot_nonzero :
    idealRoot ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰
  residual_span_eq :
    Ideal.span ({residual} : Set _) = idealRoot ^ p

private theorem parent_norm_eq_natCast_residual
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (hg : g ≠ 0) :
    norm (P.coord (g + u : ℤ) (u : ℤ)) =
      ((GTail p 1 g u : ℕ) : ℤ) := by
  rw [P.coord_norm_eq]
  have hsub : (g + u : ℤ) - (u : ℤ) = (g : ℤ) := by omega
  rw [hsub]
  have hnat :
      ((GTail p 1 g u : ℕ) : ℤ) =
        GTailCyclotomicShell p (g : ℤ) (u : ℤ) :=
    DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell hg
  exact hnat.symm

private theorem parent_norm_ne_zero
    {p g u x : ℕ} (P0 : PrimeAdicFactorPacket p g u x)
    {L : Type*} [Field L] [Algebra ℚ L]
    [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (S : PrimeAdicPowerSplit p g u x) :
    norm (P.coord (g + u : ℤ) (u : ℤ)) ≠ 0 := by
  have hnorm : norm (P.coord (g + u : ℤ) (u : ℤ)) =
      ((GTail p 1 g u : ℕ) : ℤ) :=
    parent_norm_eq_natCast_residual P P0.gap_pos.ne'
  intro hzero
  have hreszero : GTail p 1 g u = 0 := by
    apply Int.ofNat_eq_zero.mp
    rw [← hnorm]
    exact hzero
  rw [S.residual_eq] at hreszero
  have hpos : 0 < p * S.b ^ p :=
    Nat.mul_pos P0.prime.pos (Nat.pow_pos S.b_pos)
  omega

private theorem parent_natAbs_norm_eq_split
    {p g u x : ℕ} (P0 : PrimeAdicFactorPacket p g u x)
    {L : Type*} [Field L] [Algebra ℚ L]
    [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (S : PrimeAdicPowerSplit p g u x) :
    Int.natAbs (norm (P.coord (g + u : ℤ) (u : ℤ))) =
      p * S.b ^ p := by
  rw [parent_norm_eq_natCast_residual P P0.gap_pos.ne']
  rw [Int.natAbs_natCast, S.residual_eq]

private theorem ideal_ne_bot_of_generator_ne_zero
    {R : Type*} [CommRing R] {r : R} (hr : r ≠ 0) :
    Ideal.span ({r} : Set R) ≠ ⊥ := by
  intro hbot
  exact hr (Ideal.span_singleton_eq_bot.mp hbot)

private theorem ideal_root_nonzero_of_span_eq_pow
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {r : R} {I : Ideal R} {p : ℕ}
    (hr : r ≠ 0) (hp : p ≠ 0)
    (hspan : Ideal.span ({r} : Set R) = I ^ p) :
    I ∈ (Ideal R)⁰ := by
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hI
  apply ideal_ne_bot_of_generator_ne_zero hr
  rw [hspan, hI, zero_pow hp]
  simp only [Ideal.zero_eq_bot]

theorem nonempty_primeTraceOneStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    Nonempty (PrimeTraceOneStrippedIdealPacket L P0 P) := by
  let S := primeAdicPowerSplit_of_packet P0
  let parent : TraceOneInt (signedPrimeParameter p) :=
    P.coord (g + u : ℤ) (u : ℤ)
  have hparent_coprime : IsCoprime parent.fst parent.snd := by
    change IsCoprime
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ)
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ)
    exact prime_packet_coordinate_isCoprime P0 P
  have hparent_norm_ne : norm parent ≠ 0 := by
    simpa [parent] using parent_norm_ne_zero P0 P S
  have hparent_norm : Int.natAbs (norm parent) = p * S.b ^ p := by
    simpa [parent] using parent_natAbs_norm_eq_split P0 P S
  have hp2 : p ≠ 2 := by
    have hp3 := P0.odd
    omega
  let DP : PrimeDiscriminantPacket p (signedPrimeParameter p) :=
    signedPrimeDiscriminantPacket P0.prime hp2
  obtain ⟨residual, haxis, hres_norm_ne, hres_axis, hres_pow⟩ :=
    DP.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
      hparent_norm_ne hparent_norm S.prime_not_dvd_b
  have hres_coprime : IsCoprime residual.fst residual.snd :=
    coordinate_isCoprime_of_eq_discrAxis_mul haxis hparent_coprime
  letI : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField P0.prime hp2
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain P0.prime hp2
  have hideal_coprime :
      IsCoprime (Ideal.span ({residual} : Set _))
        (Ideal.span ({conj residual} : Set _)) :=
    ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
      DP hres_coprime hres_axis
  obtain ⟨k, hres_norm_pow⟩ := hres_pow
  have hideal_product :
      Ideal.span ({residual} : Set (TraceOneInt (signedPrimeParameter p))) *
        Ideal.span ({conj residual} : Set (TraceOneInt (signedPrimeParameter p))) =
      (Ideal.span ({(k : TraceOneInt (signedPrimeParameter p))} :
        Set (TraceOneInt (signedPrimeParameter p)))) ^ p :=
    span_mul_span_conj_eq_pow_of_norm_eq_pow hres_norm_pow
  obtain ⟨idealRoot, hres_span⟩ :=
    DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
      hideal_coprime hideal_product
  have hres_ne : residual ≠ 0 := by
    intro hzero
    apply hres_norm_ne
    rw [hzero]
    simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  have hroot_nonzero := ideal_root_nonzero_of_span_eq_pow
    (r := residual) hres_ne (Nat.ne_of_gt P0.prime.pos) hres_span
  refine ⟨{
    adicSplit := S
    parent := parent
    residual := residual
    axis_eq := haxis
    parent_coordinate_coprime := hparent_coprime
    residual_coordinate_coprime := hres_coprime
    residual_norm_ne_zero := hres_norm_ne
    residual_axis_terminal := hres_axis
    residual_norm_pow := ⟨k, hres_norm_pow⟩
    residual_conj_ideal_coprime := hideal_coprime
    idealRoot := idealRoot
    idealRoot_nonzero := hroot_nonzero
    residual_span_eq := hres_span }⟩

noncomputable def primeTraceOneStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    PrimeTraceOneStrippedIdealPacket L P0 P :=
  Classical.choice (nonempty_primeTraceOneStrippedIdealPacket P0 P)

end

end DkMath.FLT.Prime
