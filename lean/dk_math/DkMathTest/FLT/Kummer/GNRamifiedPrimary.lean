/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNKummerUnitAdapter

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- The full ramification assumption ell^(p-1)|p cannot be replaced by ell|p.
example : (3 : ℤ) ∣ 3 ∧ (3 : ℤ) ∣ 4 - 1 ∧ ¬ (3 : ℤ) ^ 3 ∣ 4 ^ 3 - 1 := by norm_num

-- Stripping one factor consumes exactly one level of the original gap depth.
example : ((-1 : ℤ) - 1) ^ 3 ∣ (-8 : ℤ) +
    (∑ k ∈ Finset.range 2, (-1 : ℤ) ^ k) * 1 := by
  exact stripped_phaseFactor_geom_sum_dvd_pow (ζ := (-1 : ℤ)) (x := 16) (u := 1)
    (β := -8) (by decide) 3 2 (by decide) (by decide)

example : ((-1 : ℤ) - 1) ^ 3 ∣ (8 : ℤ) ∧
    (8 : ℤ) + (1 - (-1 : ℤ) ^ 2) * 1 = ((-1 : ℤ) - 1) * (-4) ∧
    ¬ ((-1 : ℤ) - 1) ^ 3 ∣ (-4 : ℤ) +
      (∑ k ∈ Finset.range 2, (-1 : ℤ) ^ k) * 1 := by norm_num [Finset.sum_range_succ]

section Cubic
variable {K : Type*} [Field K] [NumberField K]
  [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

-- Actual nonconstant cubic generator, without a hypothetical FLT solution.
example : (hζ.toInteger - 1) ^ 3 ∣ (1 + 2 * (hζ.toInteger - 1)) ^ 3 - 1 := by
  apply prime_power_dvd_pow_sub_one_of_dvd_pred_power Nat.prime_three
  · exact (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime 3 hζ).dvd
  · exact ⟨2, by ring⟩

-- The zero index cannot provide a geometric unit.
example : (∑ k ∈ Finset.range 0, hζ.toInteger ^ k) = 0 ∧ ¬ IsUnit (0 : 𝓞 K) := by simp

example : (ramifiedGeomUnit hζ (i := 1) (by decide) : 𝓞 K) = 1 := by
  rw [ramifiedGeomUnit_val]
  simp

example : (ramifiedGeomUnit hζ (i := 2) (by decide) : 𝓞 K) = 1 + hζ.toInteger := by
  rw [ramifiedGeomUnit_val]
  simp [Finset.sum_range_succ]

example : (hζ.toInteger - 1) * (ramifiedGeomUnit hζ (i := 2) (by decide) : 𝓞 K) =
    hζ.toInteger ^ 2 - 1 := by
  rw [ramifiedGeomUnit_val, mul_geom_sum]

-- Real application of Mathlib's cubic Kummer lemma: the unit -1 is congruent to integer 2 mod 3.
example : ∃ κ : (𝓞 K)ˣ, (-1 : (𝓞 K)ˣ) = κ ^ 3 := by
  apply cubic_kummer_unit_power_criterion hζ (-1)
  refine ⟨2, (-1 : 𝓞 K), ?_⟩
  norm_num

-- A generic supplied packet now needs no extra unit-power hypothesis in the cubic case.
example {x u c : ℤ} (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 3).erase 0)
    (hγ : ramifiedReduction hζ (by decide) (Q.generator i) = 1) :
    ∃ θ : 𝓞 K, (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * θ ^ 3 :=
  factor_eq_zeta_sub_one_mul_pow_of_unit_criterion Q (by decide)
    (cubic_kummer_unit_power_criterion hζ) hi hγ
end Cubic

section Quintic
variable {K : Type*} [Field K] [NumberField K]
  [Fact (Nat.Prime 5)] [IsCyclotomicExtension {5} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 5)

example : (hζ.toInteger - 1) ^ 5 ∣ (1 - (hζ.toInteger - 1)) ^ 5 - 1 := by
  apply prime_power_dvd_pow_sub_one_of_dvd_pred_power (Fact.out : Nat.Prime 5)
  · exact (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime 5 hζ).dvd
  · exact ⟨-1, by ring⟩
end Quintic

section Packet
variable {K : Type*} [Field K] [NumberField K]
  {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}

example (P : RamifiedIdealPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    (hζ.toInteger - 1) ^ (p + 1) ∣ (x : 𝓞 K) ∧
    (hζ.toInteger - 1) ^ p ∣ P.quotient i +
      (∑ k ∈ Finset.range i, hζ.toInteger ^ k) * (u : 𝓞 K) :=
  ⟨P.ramifier_pow_succ_dvd_gap, P.quotient_geom_sum_dvd_pow_prime hi⟩

example (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ p ∣ (Q.primaryUnit hi : 𝓞 K) + (u : 𝓞 K) ∧
    (p : 𝓞 K) ∣ (Q.primaryUnit hi : 𝓞 K) - ((-u : ℤ) : 𝓞 K) ∧
    (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * ((Q.primaryUnit hi : 𝓞 K) * Q.generator i ^ p) :=
  Q.primaryUnit_spec hodd hi hγ

example (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    IsUnit (Q.primaryUnit hi : 𝓞 K) ∧
      (Q.primaryUnit hi : 𝓞 K) * (∑ k ∈ Finset.range i, hζ.toInteger ^ k) = Q.unitFactor i :=
  ⟨(Q.primaryUnit hi).isUnit, Q.primaryUnit_mul_geom_sum hi⟩

-- The sign in FLT coordinates is b, not -b.
example {a b : ℤ} (Q : RamifiedPrincipalPowerPacket hζ (a + b) (-b) c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (p : 𝓞 K) ∣ (Q.primaryUnit hi : 𝓞 K) - (b : 𝓞 K) := by
  simpa only [neg_neg] using Q.primaryUnit_congruent_integer hodd hi hγ
end Packet

#print axioms DkMath.Lib.NumberTheory.prime_power_dvd_pow_sub_one_of_dvd_pred_power
#print axioms DkMath.FLT.Kummer.cubic_kummer_unit_power_criterion
#print axioms DkMath.FLT.Kummer.exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube

run_cmd do
  for name in #[
    ``prime_power_dvd_pow_sub_one_of_dvd_pred_power,
    ``stripped_phaseFactor_geom_sum_dvd_pow,
    ``RamifiedIdealPowerPacket.ramifier_pow_succ_dvd_gap,
    ``RamifiedIdealPowerPacket.quotient_geom_sum_dvd_pow_prime,
    ``ramifier_pow_prime_dvd_generator_pow_sub_one,
    ``RamifiedPrincipalPowerPacket.unit_sub_quotient_dvd_pow_prime,
    ``RamifiedPrincipalPowerPacket.unit_geom_sum_dvd_pow_prime,
    ``ramifiedGeomUnit,
    ``ramifiedGeomUnit_val,
    ``RamifiedPrincipalPowerPacket.primaryUnit,
    ``RamifiedPrincipalPowerPacket.primaryUnit_mul_geom_sum,
    ``RamifiedPrincipalPowerPacket.primaryUnit_add_parameter_dvd_pow_prime,
    ``RamifiedPrincipalPowerPacket.primaryUnit_congruent_integer,
    ``RamifiedPrincipalPowerPacket.primaryUnit_spec,
    ``exists_GN_ramified_primary_packet,
    ``KummerUnitPowerCriterion,
    ``cubic_kummer_unit_power_criterion,
    ``factor_eq_zeta_sub_one_mul_pow_of_unit_criterion,
    ``exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion,
    ``exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
