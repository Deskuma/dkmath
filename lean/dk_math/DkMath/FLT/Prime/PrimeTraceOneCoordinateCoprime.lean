/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
import DkMath.FLT.Prime.AdicPowerSplit
import Mathlib.Tactic

#print "file: DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime"

namespace DkMath.FLT.Prime

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private theorem prime_sq_dvd_traceOne_norm
    {s a b p : ℤ} (ha : p ∣ a) (hb : p ∣ b) :
    p ^ 2 ∣ a ^ 2 + a * b - s * b ^ 2 := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  refine ⟨a' ^ 2 + a' * b' - s * b' ^ 2, ?_⟩
  ring

private theorem coordinate_prime_dvd_residual
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hA : (p : ℤ) ∣
      MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ)
    (hS : (p : ℤ) ∣
      MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ) :
    False := by
  let C := P.coord (g + u : ℤ) (u : ℤ)
  have hnorm : (p : ℤ) ^ 2 ∣ norm C := by
    change (p : ℤ) ^ 2 ∣
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ) ^ 2 +
        MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ *
          MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ -
        signedPrimeParameter p *
          (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ) ^ 2
    exact prime_sq_dvd_traceOne_norm hA hS
  have hnorm_shell : (p : ℤ) ^ 2 ∣
      GTailCyclotomicShell p ((g + u : ℤ) - (u : ℤ)) (u : ℤ) := by
    rw [← P.coord_norm_eq (g + u : ℤ) (u : ℤ)]
    exact hnorm
  have hres : (p : ℤ) ^ 2 ∣ (GTail p 1 g u : ℕ) := by
    have hshell : (p : ℤ) ^ 2 ∣
        GTailCyclotomicShell p (g : ℤ) (u : ℤ) := by
      simpa using hnorm_shell
    rw [← DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell
      P0.gap_pos.ne'] at hshell
    exact_mod_cast hshell
  exact P0.residual_not_prime_sq (by exact_mod_cast hres)

/-! ## Conditional FLT-side coordinate primitivity -/

/-- The normalized endpoint attached to a prime-adic packet is primitive. -/
theorem prime_packet_coordinate_isCoprime
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (P0 : PrimeAdicFactorPacket p g u x)
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    IsCoprime
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ)
      (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqgcd⟩ := Nat.exists_prime_and_dvd hne
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hqgcdInt : (q : ℤ) ∣
      (Int.gcd
        (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ)
        (MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ) : ℤ) := by
    exact_mod_cast hqgcd
  have hqA : (q : ℤ) ∣
      MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.AZ :=
    dvd_trans hqgcdInt (Int.gcd_dvd_left _ _)
  have hqS : (q : ℤ) ∣
      MvPolynomial.eval ![(g + u : ℤ), (u : ℤ)] P.SZ :=
    dvd_trans hqgcdInt (Int.gcd_dvd_right _ _)
  have hcop : Nat.Coprime (g + u) u :=
    (Nat.coprime_add_self_left).2 P0.coprime_gap_unit
  have hp3 := P0.odd
  have hp2 : p ≠ 2 := by omega
  have hqp : q = p := common_coordinate_prime_eq_exponent
    hp2 P hcop hqA hqS
  subst q
  exact coordinate_prime_dvd_residual P0 P hqA hqS

end

end DkMath.FLT.Prime
