/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedQuadratic

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- Concrete finite Taylor identities, without a primitive-root assumption.
example : ((3 : ℤ) - 1) ^ 2 ∣ 3 ^ 4 - 1 - 4 * (3 - 1) :=
  sub_one_sq_dvd_pow_sub_linear (3 : ℤ) 4

example : ((3 : ℤ) - 1) ^ 2 ∣ (∑ k ∈ Finset.range 4, (3 : ℤ) ^ k) - 4 - 6 * (3 - 1) :=
  sub_one_sq_dvd_geom_sum_sub_linear (3 : ℤ) 4

example : ((-1 : ℤ) - 1) ^ 2 ∣ (-4 : ℤ) + 2 + ((-1 : ℤ) - 1) := by
  exact stripped_phaseFactor_quadratic_dvd (ζ := (-1 : ℤ)) (x := 8) (u := 1)
    (β := -4) (by decide) (by decide) 2 (by decide)

-- λ²|x alone is insufficient after stripping one λ.
example : ((-1 : ℤ) - 1) ^ 2 ∣ (4 : ℤ) ∧
    (4 : ℤ) + (1 - (-1 : ℤ) ^ 2) * 1 = ((-1 : ℤ) - 1) * (-2) ∧
    ¬ ((-1 : ℤ) - 1) ^ 2 ∣ (-2 : ℤ) + 2 + ((-1 : ℤ) - 1) := by norm_num

example : (3 : ℤ) ^ 2 ∣ 4 ^ 3 - 1 := by
  exact square_dvd_pow_sub_one_of_dvd_natCast (ell := (3 : ℤ)) (γ := 4) (n := 3)
    (by norm_num) (by norm_num)

-- Both hypotheses of the power-lifting lemma are needed.
example : (3 : ℤ) ∣ (4 - 1) ∧ ¬ (3 : ℤ) ^ 2 ∣ 4 ^ 1 - 1 := by norm_num
example : (3 : ℤ) ∣ (3 : ℤ) ∧ ¬ (3 : ℤ) ^ 2 ∣ 2 ^ 3 - 1 := by norm_num

example : (3 : ℤ) ^ 2 ∣ (-1 : ℤ) - (-64) := by
  exact square_dvd_unit_sub_of_mul_pow (ell := (3 : ℤ)) (γ := 4) (n := 3)
    (by norm_num) (by norm_num) (by norm_num)

-- A square-modulus quotient really contains a nonzero square-zero class.
example : Ideal.Quotient.mk (Ideal.span ({(3 : ℤ) ^ 2} : Set ℤ)) 3 ≠ 0 ∧
    (Ideal.Quotient.mk (Ideal.span ({(3 : ℤ) ^ 2} : Set ℤ)) 3) ^ 2 = 0 :=
  prime_class_mod_square_nonzero_nilpotent (Nat.prime_iff_prime_int.mp Nat.prime_three)

section Cubic
variable {K : Type*} [Field K] [NumberField K]
  [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

example : Nat.card (𝓞 K ⧸ Ideal.span ({(hζ.toInteger - 1) ^ 2} : Set (𝓞 K))) = 9 := by
  simpa using card_ramifiedQuadraticResidue_eq_prime_sq hζ (by decide)

example : Ideal.Quotient.mk (Ideal.span ({(hζ.toInteger - 1) ^ 2} : Set (𝓞 K)))
      (hζ.toInteger - 1) ≠ 0 ∧
    (Ideal.Quotient.mk (Ideal.span ({(hζ.toInteger - 1) ^ 2} : Set (𝓞 K)))
      (hζ.toInteger - 1)) ^ 2 = 0 :=
  prime_class_mod_square_nonzero_nilpotent hζ.zeta_sub_one_prime'

-- Actual p=3, x=9, u=1 data: the extra integer depth supplies λ³|x.
example : ∃ β : 𝓞 K,
    (9 : 𝓞 K) + (1 - hζ.toInteger ^ 2) * 1 = (hζ.toInteger - 1) * β ∧
    (hζ.toInteger - 1) ^ 2 ∣ β + 2 + (hζ.toInteger - 1) := by
  have h2 : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) := by
    simpa using ramifier_sq_dvd_intCast_of_dvd_prime hζ (by decide)
      (by norm_num : (3 : ℤ) ∣ 3)
  have h1 : hζ.toInteger - 1 ∣ (3 : 𝓞 K) :=
    hζ.toInteger_isPrimitiveRoot.sub_one_dvd_natCast (by decide : 1 < 3)
  have hx : (hζ.toInteger - 1) ^ 3 ∣ (9 : 𝓞 K) := by
    convert mul_dvd_mul h2 h1 using 1 <;> ring
  obtain ⟨β, hs, _⟩ := exists_ramified_phase_quotient_of_dvd_gap hζ (by decide)
    (x := 9) (u := 1) (by norm_num) (by norm_num) (i := 2) (by decide) (by decide)
  exact ⟨β, by simpa using hs, by
    simpa using stripped_phaseFactor_quadratic_dvd (u := (1 : 𝓞 K)) (β := β)
      (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 3)) hx 2
      (by simpa using hs)⟩
end Cubic

section Packet
variable {K : Type*} [Field K] [NumberField K]
  {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}

example (P : RamifiedIdealPowerPacket hζ x u c) :
    (p : ℤ) ^ 2 ∣ x ∧ (hζ.toInteger - 1) ^ 3 ∣ (x : 𝓞 K) :=
  ⟨P.prime_sq_dvd_gap, P.ramifier_cube_dvd_gap⟩

example (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ 2 ∣ Q.unitFactor i - Q.quotient i ∧
    (hζ.toInteger - 1) ^ 2 ∣ Q.unitFactor i + (i : 𝓞 K) * (u : 𝓞 K) +
      (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (u : 𝓞 K) :=
  ⟨Q.unit_sub_quotient_sq_dvd hodd hi hγ, Q.unitFactor_quadratic_dvd hodd hi hγ⟩

-- The stronger conclusion preserves the same ideal roots, not only their existence.
example (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) :
    ∃ Q' : RamifiedPrincipalPowerPacket hζ x u c,
      Q'.toRamifiedIdealPowerPacket = Q.toRamifiedIdealPowerPacket ∧
      Q'.idealRoot = Q.idealRoot ∧
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q'.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q'.unitFactor i) = -(i : ZMod p) * (u : ZMod p) ∧
        (hζ.toInteger - 1) ^ 2 ∣ Q'.unitFactor i + (i : 𝓞 K) * (u : 𝓞 K) +
          (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (u : 𝓞 K) := by
  obtain ⟨Q', hbase, hquad⟩ := Q.exists_quadratic_normalization hodd
  exact ⟨Q', hbase, congrArg RamifiedIdealPowerPacket.idealRoot hbase, hquad⟩
end Packet

#print axioms DkMath.Lib.NumberTheory.RamifiedIdealPowerPacket.prime_sq_dvd_gap
#print axioms DkMath.FLT.Kummer.exists_GN_ramified_quadratic_normalized_packet

run_cmd do
  for name in #[
    ``sub_one_sq_dvd_pow_sub_linear,
    ``sub_one_sq_dvd_geom_sum_sub_linear,
    ``stripped_phaseFactor_quadratic_dvd,
    ``square_dvd_pow_sub_one_of_dvd_natCast,
    ``square_dvd_unit_sub_of_mul_pow,
    ``prime_class_mod_square_nonzero_nilpotent,
    ``card_ramifiedQuadraticResidue_eq_prime_sq,
    ``RamifiedIdealPowerPacket.prime_sq_dvd_gap,
    ``RamifiedIdealPowerPacket.ramifier_cube_dvd_gap,
    ``RamifiedIdealPowerPacket.quotient_quadratic_dvd,
    ``RamifiedPrincipalPowerPacket.unit_sub_quotient_sq_dvd,
    ``RamifiedPrincipalPowerPacket.unitFactor_quadratic_dvd,
    ``RamifiedPrincipalPowerPacket.exists_quadratic_normalization,
    ``exists_GN_ramified_quadratic_normalized_packet] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
