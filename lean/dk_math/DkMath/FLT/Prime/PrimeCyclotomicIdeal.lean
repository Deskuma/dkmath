/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.CyclotomicIdeal
import DkMath.FLT.Prime.AdicPowerSplit
import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core

#print "file: DkMath.FLT.Prime.PrimeCyclotomicIdeal"

/-!
# Generic FLT packet adapter for the cyclotomic ideal carrier

This module changes the representation of the existing generic FLT arithmetic
packets.  It does not add a local prime-ideal factorization, principalization,
or a new p-th-power argument.
-/

namespace DkMath.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula

noncomputable section

/-! ## Prime-adic factor packet -/

/-- The cyclotomic ideal norm is the residual `GTail` of the packet. -/
theorem PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (_P : PrimeAdicFactorPacket p g u x) :
    Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) =
      GTail p 1 g u := by
  simpa [DkMath.CosmicFormulaBinom.GN] using
    (cyclotomicLinearFactorIdeal_absNorm_eq_GN
      (p := p) (x := g) (u := u) hζ)

/-- The packet's distinguished `x^p` equation through the cyclotomic ideal.

The packet supplies `x^p = g * GTail p 1 g u`; replacing the residual `GTail`
by the absolute norm of the canonical cyclotomic ideal transfers the same
factor equation to the new carrier without introducing a prime-ideal choice. -/
theorem PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : PrimeAdicFactorPacket p g u x) :
    g * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) = x ^ p := by
  calc
    g * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) =
        g * GTail p 1 g u := by
          rw [P.cyclotomicIdeal_absNorm_eq_residual hζ]
    _ = x ^ p := P.factor_eq

/-- The packet's residual valuation transported to the cyclotomic ideal. -/
theorem PrimeAdicFactorPacket.padicValNat_cyclotomicIdeal_absNorm_eq_one
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : PrimeAdicFactorPacket p g u x) :
    padicValNat p (Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u)) = 1 := by
  calc
    padicValNat p (Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u)) =
        padicValNat p (GTail p 1 g u) := by
          rw [P.cyclotomicIdeal_absNorm_eq_residual hζ]
    _ = 1 := P.residual_exact_one

/-- The packet's residual divisibility transported to the cyclotomic ideal. -/
theorem PrimeAdicFactorPacket.prime_dvd_cyclotomicIdeal_absNorm
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : PrimeAdicFactorPacket p g u x) :
    p ∣ Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) := by
  rw [P.cyclotomicIdeal_absNorm_eq_residual hζ]
  exact P.prime_dvd_residual

/-- The packet's exact residual valuation excludes a squared rational prime. -/
theorem PrimeAdicFactorPacket.prime_sq_not_dvd_cyclotomicIdeal_absNorm
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : PrimeAdicFactorPacket p g u x) :
    ¬ p ^ 2 ∣ Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) := by
  rw [P.cyclotomicIdeal_absNorm_eq_residual hζ]
  exact P.residual_not_prime_sq

/-! ## Ramified power split -/

/-- The ramified power split's residual normal form through the ideal norm. -/
theorem PrimeAdicPowerSplit.cyclotomicIdeal_absNorm_eq_prime_mul_pow
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : PrimeAdicPowerSplit p g u x) :
    Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) = p * S.b ^ p := by
  calc
    Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) =
        GTail p 1 g u := S.input.cyclotomicIdeal_absNorm_eq_residual hζ
    _ = p * S.b ^ p := S.residual_eq

/-! ## Prime-ge5 counterexample adapter -/

/-- A ramified prime-ge5 counterexample supplies the generic adic packet.

The divisibility assumption is local to this constructor; no global
`p ∣ gap` assumption is added to the counterexample pack. -/
theorem PrimeGe5CounterexamplePack.toPrimeAdicFactorPacket_of_prime_dvd_gap
    {p x y z : ℕ}
    (h : DkMath.FLT.PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ h.gap) :
    PrimeAdicFactorPacket p h.gap y x := by
  refine
    { prime := h.hp
      odd := le_trans (by norm_num) h.hp5
      gap_pos := h.gap_pos
      distinguished_pos := h.x_pos
      coprime_gap_unit := h.gap_coprime_right
      prime_dvd_gap := hp_dvd_gap
      factor_eq := ?_ }
  simpa [DkMath.CosmicFormulaBinom.GN] using h.xpow_eq_gap_mul_GN.symm

/-- Every prime-ge5 counterexample pack reaches the cyclotomic ideal carrier,
independently of the away/ramified branch. -/
theorem PrimeGe5CounterexamplePack.gap_mul_cyclotomicIdeal_absNorm_eq_pow
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (h : DkMath.FLT.PrimeGe5CounterexamplePack p x y z) :
    h.gap * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ h.gap y) = x ^ p := by
  calc
    h.gap * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ h.gap y) =
        h.gap * DkMath.CosmicFormulaBinom.GN p h.gap y := by
          rw [cyclotomicLinearFactorIdeal_absNorm_eq_GN hζ]
    _ = x ^ p := h.xpow_eq_gap_mul_GN.symm

end

end DkMath.FLT.Prime
