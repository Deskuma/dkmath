/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

/-- Unit cancellation uses 49 = 1 + 6 * 8. The modulus need not be prime;
the zero and one moduli are included. -/
theorem exists_sixth_power_residue_of_fortyNinth_power {r s w : ℕ}
    (hcop : Nat.Coprime r s) (h : Nat.ModEq (r ^ 49) (s ^ 49) (w ^ 6)) :
    ∃ t : ℕ, Nat.ModEq (r ^ 49) (t ^ 6) s := by
  by_cases hr : r = 0
  · subst r
    have hs : s = 1 := by simpa using hcop
    subst s
    exact ⟨1, by simp [Nat.ModEq]⟩
  · let : NeZero (r ^ 49) := ⟨pow_ne_zero 49 hr⟩
    let i : ZMod (r ^ 49) := (s : ZMod (r ^ 49))⁻¹
    have hsi : (s : ZMod (r ^ 49)) * i = 1 :=
      ZMod.coe_mul_inv_eq_one s (hcop.pow_left 49).symm
    have hc : (s : ZMod (r ^ 49)) ^ 49 = (w : ZMod (r ^ 49)) ^ 6 := by
      have h' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
      simpa only [Nat.cast_pow] using h'
    let a : ZMod (r ^ 49) := (w : ZMod (r ^ 49)) * i ^ 8
    have ha : a ^ 6 = (s : ZMod (r ^ 49)) := by
      dsimp [a]
      rw [mul_pow, ← pow_mul, ← hc]
      calc
        (s : ZMod (r ^ 49)) ^ 49 * i ^ (8 * 6) =
            (s : ZMod (r ^ 49)) * ((s : ZMod (r ^ 49)) * i) ^ 48 := by ring
        _ = (s : ZMod (r ^ 49)) := by rw [hsi]; simp
    refine ⟨a.val, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using ha

/-- An endpoint-independent necessary condition; it does not assert either
exact scalar equation. -/
def SixthPowerAllocationSieve (r s : ℕ) : Prop :=
  ∃ t : ℕ, Nat.ModEq (r ^ 49) (t ^ 6) s

theorem sixthPowerAllocationSieve_mod_one (s : ℕ) : SixthPowerAllocationSieve 1 s := by
  exact ⟨0, by simp [Nat.ModEq, Nat.mod_one]⟩

theorem nested_full_gap_sixth_power_sieve {r s w : ℕ} (hcop : Nat.Coprime r s)
    (h : Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (w ^ 6)) :
    SixthPowerAllocationSieve r s :=
  exists_sixth_power_residue_of_fortyNinth_power hcop
    (h.of_dvd (dvd_mul_left (r ^ 49) (7 ^ 27)))

theorem nestedAllocation_sixth_power_sieve {M r : ℕ} (hcop : Nat.Coprime r (M / r))
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    SixthPowerAllocationSieve r (M / r) := by
  rcases h with ⟨u, _, _, hGN⟩ | ⟨u, _, huD, _, hAlt⟩
  · exact nested_full_gap_sixth_power_sieve hcop (nestedResidual_full_gap_congruence hGN)
  · have hsum : (7 ^ 27 * r ^ 49 - u) + u = 7 ^ 27 * r ^ 49 := by omega
    have hAlt' : alternatingCyclotomicSeven (7 ^ 27 * r ^ 49 - u) u =
        7 * (M / r) ^ 49 := by
      rw [alternatingCyclotomicSeven_comm]; exact hAlt
    exact nested_full_gap_sixth_power_sieve hcop
      (nestedAlternatingResidual_full_sum_congruence hsum hAlt').2

theorem nestedAllocation_excluded_of_sixth_power {M r : ℕ}
    (hcop : Nat.Coprime r (M / r)) (hbad : ¬ SixthPowerAllocationSieve r (M / r)) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :=
  fun h => hbad (nestedAllocation_sixth_power_sieve hcop h)

/-- Reduction works for every divisor, so in particular for each prime in
the allocation's support. -/
theorem sixthPowerAllocationSieve_reduce {q r s : ℕ} (hqr : q ∣ r)
    (h : SixthPowerAllocationSieve r s) : ∃ t : ℕ, Nat.ModEq q (t ^ 6) s := by
  rcases h with ⟨t, ht⟩
  exact ⟨t, ht.of_dvd (dvd_pow hqr (by decide : 49 ≠ 0))⟩

theorem sixthPowerAllocationSieve_mod_three {r s : ℕ} (hcop : Nat.Coprime r s)
    (h3r : 3 ∣ r) (h : SixthPowerAllocationSieve r s) : Nat.ModEq 3 s 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hs : ¬ 3 ∣ s := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left h3r)
  rcases sixthPowerAllocationSieve_reduce h3r h with ⟨t, ht⟩
  have htu : ¬ 3 ∣ t := by
    intro h3t
    have ht0 : Nat.ModEq 3 (t ^ 6) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow h3t (by decide : 6 ≠ 0))
    exact hs (Nat.modEq_zero_iff_dvd.mp (ht.symm.trans ht0))
  have ht2 : Nat.ModEq 3 (t ^ 2) 1 := by
    simpa using Nat.ModEq.pow_card_sub_one_eq_one hp
      (hp.coprime_iff_not_dvd.mpr htu).symm
  have ht6 : Nat.ModEq 3 (t ^ 6) 1 := by
    simpa only [← pow_mul, one_pow] using ht2.pow 3
  exact ht.symm.trans ht6

theorem nestedAllocation_mod_three {M r : ℕ} (hcop : Nat.Coprime r (M / r))
    (h3r : 3 ∣ r)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 3 (M / r) 1 :=
  sixthPowerAllocationSieve_mod_three hcop h3r (nestedAllocation_sixth_power_sieve hcop h)

/-- All preceding guards and exact endpoint predicates are retained; only
the necessary allocation residue support is added. -/
def SixthPowerSievedNestedCondition (M : ℕ) : Prop :=
  ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 7 (M / r) 1 ∧ SixthPowerAllocationSieve r (M / r) ∧
    ((7 ^ 161 * r ^ 343 < M ^ 49 ∧ NestedGNAllocationCondition M r) ∨
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49 ∧
        NestedRHSAllocationCondition M r))

theorem residueSievedNestedCondition_iff_sixth_power_sieved (M : ℕ) :
    ResidueSievedNestedCondition M ↔ SixthPowerSievedNestedCondition M := by
  constructor
  · rintro ⟨r, hmem, hcop, hsize, h7, h⟩
    have hbranch : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r :=
      h.elim (fun h => .inl h.2) (fun h => .inr h.2.2)
    exact ⟨r, hmem, hcop, hsize, h7, nestedAllocation_sixth_power_sieve hcop hbranch, h⟩
  · rintro ⟨r, hmem, hcop, hsize, h7, _, h⟩
    exact ⟨r, hmem, hcop, hsize, h7, h⟩

/-- The coprime complementary-root identity localizes eligible support:
it avoids N and occurs in one of the two outer roots. -/
theorem allocation_prime_support_of_coprime_product {M N V C r q : ℕ}
    (hproduct : M * N = V * C) (hcop : Nat.Coprime M N)
    (hprime : Nat.Prime q) (hqr : q ∣ r) (hrM : r ∣ M) :
    ¬ q ∣ N ∧ (q ∣ V ∨ q ∣ C) := by
  have hqM : q ∣ M := hqr.trans hrM
  refine ⟨hprime.coprime_iff_not_dvd.mp (hcop.of_dvd_left hqM), ?_⟩
  apply hprime.dvd_mul.mp
  rw [← hproduct]
  exact dvd_mul_of_dvd_left hqM N

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourReconstruction_iff_sixth_power_sieved
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      SixthPowerSievedNestedCondition (internalDepthFourSeventhCore p) := by
  rw [internalDepthFourReconstruction_iff_residue_sieved,
    residueSievedNestedCondition_iff_sixth_power_sieved]

theorem internalDepthFourAllocation_prime_support (p : RamifiedSignedRootRoutingPacket)
    {r q : ℕ} (hmem : r ∈ (internalDepthFourSeventhCore p).divisors)
    (hprime : Nat.Prime q) (hqr : q ∣ r) :
    let packet := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
    ∃ N : ℕ, 0 < N ∧ internalDepthFourSeventhCore p * N =
      packet.quadratic.canonical.verticalGapRoot * packet.quadratic.compensationRoot ∧
      Nat.Coprime (internalDepthFourSeventhCore p) N ∧ ¬ 7 ∣ N ∧ ¬ q ∣ N ∧
      (q ∣ packet.quadratic.canonical.verticalGapRoot ∨
        q ∣ packet.quadratic.compensationRoot) := by
  let packet := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  rcases packet.exists_inner_complementary_seventh_root with
    ⟨N, hN, _, hproduct, hcop, h7⟩
  change internalDepthFourSeventhCore p * N = _ at hproduct
  change Nat.Coprime (internalDepthFourSeventhCore p) N at hcop
  have hsupp := allocation_prime_support_of_coprime_product hproduct hcop hprime hqr
    (Nat.dvd_of_mem_divisors hmem)
  exact ⟨N, hN, hproduct, hcop, h7, hsupp⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
