/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

#print "file: DkMath.NumberTheory.Legendre.ParitySafeMobiusWave"

/-!
## ParitySafeMobiusWave

This module opens the finite reduced-residue count from PRIM-L037 by
Möbius inclusion-exclusion.  The resulting identities are signed integer
equalities: they expose exact divisor-floor cancellation, but do not give a
bound for that cancellation or a proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped ArithmeticFunction.Moebius BigOperators

/-! ### PRIM-L038.1: finite divisor-floor scaffolding -/

private theorem sum_moebius_divisors_eq_indicator (m : ℕ) :
    (∑ d ∈ m.divisors, ArithmeticFunction.moebius d : ℤ) =
      if m = 1 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
      have h := congrArg (fun f : ArithmeticFunction ℤ => f (m + 1))
        ArithmeticFunction.coe_zeta_mul_moebius
      rw [← ArithmeticFunction.coe_zeta_mul_apply]
      exact h

private theorem divisors_filter_dvd_gcd
    {M k : ℕ} (hM : 0 < M) :
    M.divisors.filter (fun d => d ∣ k) = (M.gcd k).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdM, _⟩, hdk⟩
    exact ⟨Nat.dvd_gcd hdM hdk, Nat.gcd_ne_zero_left hM.ne'⟩
  · intro hdg
    exact ⟨⟨Nat.dvd_trans hdg.1 (Nat.gcd_dvd_left M k), hM.ne'⟩,
      Nat.dvd_trans hdg.1 (Nat.gcd_dvd_right M k)⟩

private theorem card_filter_dvd_Ioc_eq_sub_div
    {A B d : ℕ} (hAB : A ≤ B) :
    ((Finset.Ioc A B).filter (fun k => d ∣ k)).card = B / d - A / d := by
  have ht :
      (Finset.Ioc A B).filter (fun k => d ∣ k) =
        (Finset.Ioc 0 B).filter (fun k => d ∣ k) \
          (Finset.Ioc 0 A).filter (fun k => d ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
    omega
  have hsub :
      (Finset.Ioc 0 A).filter (fun k => d ∣ k) ⊆
        (Finset.Ioc 0 B).filter (fun k => d ∣ k) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIoc, hdk⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hdk⟩
    have hkIoc' := Finset.mem_Ioc.mp hkIoc
    exact Finset.mem_Ioc.mpr ⟨hkIoc'.1, by omega⟩
  rw [ht, Finset.card_sdiff_of_subset hsub]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]

/-! ### PRIM-L038.2: the generic exact signed count -/

/--
The reduced-residue count in a finite interval is an exact Möbius
divisor-floor sum.  This is a finite identity in `ℤ`; in particular, no
estimate for the signed correction is included in the statement.
-/
theorem card_filter_coprime_Ioc_eq_sum_moebius_div
    {M A B : ℕ} (hM : 0 < M) (hAB : A ≤ B) :
    (((Finset.Ioc A B).filter (fun k => Nat.Coprime M k)).card : ℤ) =
      ∑ d ∈ M.divisors,
        ArithmeticFunction.moebius d *
          (((B / d : ℕ) : ℤ) - ((A / d : ℕ) : ℤ)) := by
  classical
  let S : Finset ℕ := Finset.Ioc A B
  have hpoint (k : ℕ) :
      (if Nat.Coprime M k then (1 : ℤ) else 0) =
        ∑ d ∈ M.divisors, if d ∣ k then ArithmeticFunction.moebius d else 0 := by
    have hfilter := divisors_filter_dvd_gcd hM (k := k)
    have hsum :
        (∑ d ∈ M.divisors, if d ∣ k then ArithmeticFunction.moebius d else 0) =
          ∑ d ∈ (M.gcd k).divisors, ArithmeticFunction.moebius d := by
      rw [← Finset.sum_filter]
      exact congrArg (fun t => ∑ d ∈ t, ArithmeticFunction.moebius d) hfilter
    rw [hsum, sum_moebius_divisors_eq_indicator]
  have hsum_points :
      (∑ k ∈ S, if Nat.Coprime M k then (1 : ℤ) else 0) =
        ∑ k ∈ S, ∑ d ∈ M.divisors,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpoint k
  calc
    (((Finset.Ioc A B).filter (fun k => Nat.Coprime M k)).card : ℤ) =
        ∑ k ∈ S, if Nat.Coprime M k then (1 : ℤ) else 0 := by
      change (((S.filter (fun k => Nat.Coprime M k)).card : ℤ)) =
        ∑ k ∈ S, if Nat.Coprime M k then (1 : ℤ) else 0
      exact Finset.natCast_card_filter (R := ℤ)
        (fun k => Nat.Coprime M k) S
    _ = ∑ k ∈ S, ∑ d ∈ M.divisors,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := hsum_points
    _ = ∑ d ∈ M.divisors, ∑ k ∈ S,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ M.divisors,
          ArithmeticFunction.moebius d *
            (((B / d : ℕ) : ℤ) - ((A / d : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      have hcard := card_filter_dvd_Ioc_eq_sub_div (d := d) hAB
      dsimp [S]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const]
      rw [hcard]
      have hdiv : A / d ≤ B / d := Nat.div_le_div_right hAB
      simp only [nsmul_eq_mul]
      change ((B / d - A / d : ℕ) : ℤ) * ArithmeticFunction.moebius d =
        ArithmeticFunction.moebius d *
          (((B / d : ℕ) : ℤ) - ((A / d : ℕ) : ℤ))
      rw [Nat.cast_sub hdiv]
      ring

/-! ### PRIM-L038.3: the active-wave specialization -/

/--
The L037 wave/quotient bijection transports the generic reduced-residue
Möbius ledger to one active parity-safe prime wave.
-/
theorem paritySafeActiveWave_card_eq_mobius_divisor_floor_sum
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    ((paritySafeActiveWaveOffsets n q).card : ℤ) =
      ∑ d ∈ (2 * n).divisors, ArithmeticFunction.moebius d *
        (((((n ^ 2 + 2 * n) / q) / d : ℕ) : ℤ) -
          (((n ^ 2 / q) / d : ℕ) : ℤ)) := by
  have hq' := activePrime_reducedResidue_packet hq
  have hn : 0 < n := lt_of_lt_of_le hq'.1.pos hq'.2.1
  have hcard := card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq
  rw [hcard]
  exact card_filter_coprime_Ioc_eq_sum_moebius_div
    (by omega) (Nat.div_le_div_right (by omega))

/-! ### PRIM-L038.4: the global signed incidence ledger -/

/-- The nonnegative floor difference occurring in the wave ledger. -/
def paritySafeQuotientDivisorFloorDelta (n q d : ℕ) : ℕ :=
  ((n ^ 2 + 2 * n) / q) / d - (n ^ 2 / q) / d

/--
The global incidence count is the finite sum of the wave Möbius ledgers.
The second equality is the divisor-first transpose of the same signed sum.
-/
theorem paritySafeIncidenceCount_eq_mobius_wave_sum
    {n : ℕ} :
    (paritySafeIncidenceCount n : ℤ) =
      ∑ q ∈ squareAnchorOddActivePrimes n,
        ∑ d ∈ (2 * n).divisors, ArithmeticFunction.moebius d *
          (paritySafeQuotientDivisorFloorDelta n q d : ℤ) := by
  classical
  rw [show paritySafeIncidenceCount n =
      ∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeActiveWaveOffsets n q).card by rfl]
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  rw [paritySafeActiveWave_card_eq_mobius_divisor_floor_sum hq]
  apply Finset.sum_congr rfl
  intro d hd
  have hq' := activePrime_reducedResidue_packet hq
  have hle : (n ^ 2 / q) / d ≤ (n ^ 2 + 2 * n) / q / d :=
    Nat.div_le_div_right (Nat.div_le_div_right (by omega))
  unfold paritySafeQuotientDivisorFloorDelta
  rw [Nat.cast_sub hle]

theorem paritySafeIncidenceCount_eq_mobius_divisor_first_sum
    {n : ℕ} :
    (paritySafeIncidenceCount n : ℤ) =
      ∑ d ∈ (2 * n).divisors, ArithmeticFunction.moebius d *
        ∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeQuotientDivisorFloorDelta n q d : ℤ) := by
  rw [paritySafeIncidenceCount_eq_mobius_wave_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.mul_sum]

/-! ### PRIM-L038.5: a concrete signed cancellation witness -/

/-- The wave at `n = 5`, `q = 3` has exactly the two seats `27` and `33`. -/
theorem paritySafeActiveWaveOffsets_five_three_card :
    (paritySafeActiveWaveOffsets 5 3).card = 2 := by
  have hq : 3 ∈ squareAnchorOddActivePrimes 5 := by
    norm_num [squareAnchorOddActivePrimes]
  rw [card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq]
  decide

/-- The corresponding Möbius divisor-floor sum evaluates to the same count. -/
theorem paritySafeActiveWaveOffsets_five_three_mobius_sum :
    ∑ d ∈ (2 * 5).divisors, ArithmeticFunction.moebius d *
        (((((5 ^ 2 + 2 * 5) / 3) / d : ℕ) : ℤ) -
          (((5 ^ 2 / 3) / d : ℕ) : ℤ)) = 2 := by
  have hq : 3 ∈ squareAnchorOddActivePrimes 5 := by
    norm_num [squareAnchorOddActivePrimes]
  rw [← paritySafeActiveWave_card_eq_mobius_divisor_floor_sum hq]
  exact_mod_cast paritySafeActiveWaveOffsets_five_three_card

end DkMath.NumberTheory.Legendre
