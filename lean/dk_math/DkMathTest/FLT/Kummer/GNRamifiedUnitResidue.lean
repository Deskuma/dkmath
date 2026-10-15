/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedUnitResidue

open scoped NumberField
open DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- The stripped-factor congruence is a ring identity, not specific to number fields.
example : (-1 : ℤ) - 1 ∣ (-3 : ℤ) + (1 : ℤ) * 1 := by
  exact stripped_phaseFactor_add_index_mul_dvd (ζ := (-1 : ℤ)) (x := 4) (u := 1)
    (β := -3) (by norm_num) (by norm_num) 1 (by norm_num)

-- Mere λ divisibility of x cannot replace λ² divisibility.
example : (-1 : ℤ) - 1 ∣ (2 : ℤ) ∧
    (2 : ℤ) + (1 - (-1 : ℤ) ^ 1) * 1 = ((-1 : ℤ) - 1) * (-2) ∧
    ¬ (-1 : ℤ) - 1 ∣ (-2 : ℤ) + 1 := by norm_num

section Cubic
variable {K : Type*} [Field K] [NumberField K]
  [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

example : Nat.card (𝓞 K ⧸ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) = 3 :=
  card_ramifiedResidue_eq_prime hζ (by decide)

example : ramifiedReduction hζ (by decide) hζ.toInteger = 1 :=
  ramifiedReduction_zeta hζ (by decide)

example : ramifiedReduction hζ (by decide) (-7 : 𝓞 K) = (2 : ZMod 3) := by
  rw [map_neg, map_ofNat]
  have h := (ZMod.intCast_eq_intCast_iff (-7) 2 3).mpr (by decide)
  simpa only [Int.cast_neg, Int.cast_ofNat] using h

example : ramifiedReduction hζ (by decide) (1 + hζ.toInteger) = (2 : ZMod 3) := by
  rw [map_add, map_one, ramifiedReduction_zeta]
  norm_num

example (a : 𝓞 K) :
    ramifiedReduction hζ (by decide) (a + (hζ.toInteger - 1)) =
      ramifiedReduction hζ (by decide) a := by
  apply (ramifiedReduction_eq_iff hζ (by decide) _ _).mpr
  convert dvd_refl (hζ.toInteger - 1) using 1
  ring

-- The residue 2 is lifted to a genuine global unit via a cyclotomic geometric sum.
example : ∃ e : (𝓞 K)ˣ, ramifiedReduction hζ (by decide) (e : 𝓞 K) = (2 : ZMod 3) := by
  obtain ⟨e, he⟩ := exists_unit_lift_ramifiedResidue hζ (by decide)
    (Units.mk0 (2 : ZMod 3) (by
      intro h
      have hd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
      norm_num at hd))
  exact ⟨e, he⟩

-- Actual ramified factors at x=3,u=1 show the dependence on the index.
example : ∃ β : 𝓞 K,
    (3 : 𝓞 K) + (1 - hζ.toInteger ^ 1) * 1 = (hζ.toInteger - 1) * β ∧
      ramifiedReduction hζ (by decide) β = -(1 : ZMod 3) := by
  obtain ⟨β, hs, _⟩ := exists_ramified_phase_quotient_of_dvd_gap hζ (by decide)
    (x := 3) (u := 1) (by norm_num) (by norm_num) (i := 1) (by decide) (by decide)
  exact ⟨β, by simpa using hs, by
    simpa using ramifiedReduction_stripped_phaseFactor hζ (by decide) (by decide)
      (by norm_num : (3 : ℤ) ∣ 3) 1 hs⟩

example : ∃ β : 𝓞 K,
    (3 : 𝓞 K) + (1 - hζ.toInteger ^ 2) * 1 = (hζ.toInteger - 1) * β ∧
      ramifiedReduction hζ (by decide) β = (1 : ZMod 3) := by
  obtain ⟨β, hs, _⟩ := exists_ramified_phase_quotient_of_dvd_gap hζ (by decide)
    (x := 3) (u := 1) (by norm_num) (by norm_num) (i := 2) (by decide) (by decide)
  refine ⟨β, by simpa using hs, ?_⟩
  have hred := ramifiedReduction_stripped_phaseFactor hζ (by decide) (by decide)
    (by norm_num : (3 : ℤ) ∣ 3) 2 hs
  norm_num at hred ⊢
  exact hred

-- Normalize the negative generator γ=-1, β=-1, ε=1; β is fixed and γ is changed by a unit.
example : ∃ (ε γ : 𝓞 K) (e : (𝓞 K)ˣ), IsUnit ε ∧ (-1 : 𝓞 K) = ε * γ ^ 3 ∧
    ramifiedReduction hζ (by decide) γ = 1 ∧ ramifiedReduction hζ (by decide) ε = -1 ∧
    γ = (e : 𝓞 K) * (-1) ∧ ε = (↑(e⁻¹) : 𝓞 K) ^ 3 := by
  have hβ : ¬ hζ.toInteger - 1 ∣ (-1 : 𝓞 K) := by
    intro h
    have hd : (3 : ℤ) ∣ -1 :=
      (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' 3 hζ).mp (by simpa using h)
    norm_num at hd
  obtain ⟨ε, γ, hε, _, hpow, hγ, hεred, e, heγ, heε⟩ :=
    exists_residue_normalized_unit_mul_pow hζ (by decide) hβ isUnit_one
      (γ := (-1 : 𝓞 K)) (by norm_num)
  exact ⟨ε, γ, e, hε, hpow, hγ, by simpa using hεred, heγ, by simpa using heε⟩
end Cubic

-- The entire old ideal packet survives the normalization unchanged.
example {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) :
    ∃ Q' : RamifiedPrincipalPowerPacket hζ x u c,
      Q'.toRamifiedIdealPowerPacket = Q.toRamifiedIdealPowerPacket ∧ Q'.idealRoot = Q.idealRoot ∧
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q'.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q'.unitFactor i) = -(i : ZMod p) * (u : ZMod p) := by
  obtain ⟨Q', hbase, hred⟩ := Q.exists_residue_normalization hodd
  exact ⟨Q', hbase, congrArg RamifiedIdealPowerPacket.idealRoot hbase, hred⟩

#print axioms DkMath.Lib.NumberTheory.exists_residue_normalized_unit_mul_pow
#print axioms DkMath.FLT.Kummer.exists_GN_ramified_residue_normalized_packet

run_cmd do
  for name in #[
    ``sub_one_dvd_geom_sum_sub_nat,
    ``stripped_phaseFactor_add_index_mul_dvd,
    ``card_ramifiedResidue_eq_prime,
    ``ramifiedResidueEquiv,
    ``ramifiedReduction,
    ``ramifiedReduction_eq_zero_iff,
    ``ramifiedReduction_eq_iff,
    ``ramifiedReduction_zeta,
    ``ramifier_sq_dvd_intCast_of_dvd_prime,
    ``ramifiedReduction_stripped_phaseFactor,
    ``ramifiedReduction_geom_sum,
    ``exists_unit_lift_ramifiedResidue,
    ``exists_residue_normalized_unit_mul_pow,
    ``RamifiedIdealPowerPacket.quotient_reduction,
    ``RamifiedPrincipalPowerPacket.exists_residue_normalization,
    ``RamifiedIdealPowerPacket.exists_residue_normalized_principal_extension,
    ``exists_GN_ramified_residue_normalized_packet] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
