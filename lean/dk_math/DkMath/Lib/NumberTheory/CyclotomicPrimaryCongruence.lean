/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Ramified-prime arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: the specified primitive root and field are retained, residue powers use
Mathlib finite-field cardinality directly, and DkMath supplies the local condition.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence"

/-!
# 同じ原始根の分岐素点における具体的な3次の合同

指定した数体 F と指定した原始根 ζ に対し、同じ素点 (ζ−1) を取る。
p の分岐と剰余体の濃度 p を Mathlib から導き、局所 p 乗条件から
同じ単元の u^(p−1)−1∈(ζ−1)^3 を得る。単元固有空間の消滅はまだ主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence

open NumberField IsDedekindDomain HeightOneSpectrum CyclotomicPrimaryUnitSpace
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 選び直していない同じ原始根から作る分岐イデアル。 -/
def ramifiedIdeal : Ideal (𝓞 F) := Ideal.span {hζ.toInteger - 1}

/-- 同じ分岐イデアルを、非零素点として構成する。 -/
def ramifiedPlace : HeightOneSpectrum (𝓞 F) where
  asIdeal := ramifiedIdeal hζ
  isPrime := IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' p hζ
  ne_bot := by
    rw [ramifiedIdeal, ne_eq, Ideal.span_singleton_eq_bot]
    exact hζ.zeta_sub_one_prime'.ne_zero

/-- 実際の p の分岐次数 p−1 から、指定した深さ n への所属を得る。 -/
theorem natCast_mem_ramifiedIdeal_pow (n : ℕ) (hn : n ≤ p - 1) :
    (p : 𝓞 F) ∈ ramifiedIdeal hζ ^ n := by
  have hK : IsCyclotomicExtension {p ^ (0 + 1)} ℚ F := by simpa using
    (inferInstance : IsCyclotomicExtension {p} ℚ F)
  have hroot : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  have hmap := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hroot
  have hfin : Module.finrank ℚ F = p - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank p F, Nat.totient_prime (Fact.out : p.Prime)]
  have hmem : (p : 𝓞 F) ∈ Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) := by
    simpa using Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 F)) (Ideal.mem_span_singleton_self (p : ℤ))
  rw [hmap, hfin] at hmem
  exact Ideal.pow_le_pow_right hn hmem

/-- 同じ分岐素点の実際の剰余体は p 個の元を持つ。 -/
theorem ramified_residue_card : Nat.card (𝓞 F ⧸ (ramifiedPlace hζ).asIdeal) = p := by
  have hK : IsCyclotomicExtension {p ^ (0 + 1)} ℚ F := by simpa using
    (inferInstance : IsCyclotomicExtension {p} ℚ F)
  have hroot : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  have h := IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hroot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  exact h

/-- 同じ整数環単元の剰余は、同じ剰余体で p−1 乗が1になる。 -/
theorem unit_pow_sub_one_mem_ramifiedIdeal (u : (𝓞 F)ˣ) :
    (u : 𝓞 F) ^ (p - 1) - 1 ∈ ramifiedIdeal hζ := by
  let vF := ramifiedPlace hζ
  let : Field (𝓞 F ⧸ vF.asIdeal) := Ideal.Quotient.field vF.asIdeal
  let : Finite (𝓞 F ⧸ vF.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient vF.ne_bot
  let : Fintype (𝓞 F ⧸ vF.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ vF.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact ramified_residue_card hζ
  have hu : IsUnit (Ideal.Quotient.mk vF.asIdeal (u : 𝓞 F)) :=
    u.isUnit.map (Ideal.Quotient.mk vF.asIdeal)
  change (u : 𝓞 F) ^ (p - 1) - 1 ∈ vF.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  simpa only [hcard] using FiniteField.pow_card_sub_one_eq_one
    (Ideal.Quotient.mk vF.asIdeal (u : 𝓞 F)) hu.ne_zero

/-- 局所冪の共通核に属する同じ単元は、指定した根の分岐素点で3次合同を満たす。 -/
theorem pow_sub_one_mem_ramifiedIdeal_cube_of_local_power (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ)
    (hloc : Additive.ofMul (u : KummerSelmerExact.UnitClass (𝓞 F) p) ∈ localPowerSpace F p) :
    (u : 𝓞 F) ^ (p - 1) - 1 ∈ ramifiedIdeal hζ ^ 3 := by
  have hpv : (p : 𝓞 F) ∈ (ramifiedPlace hζ).asIdeal := by
    change (p : 𝓞 F) ∈ ramifiedIdeal hζ
    simpa only [pow_one] using natCast_mem_ramifiedIdeal_pow hζ 1 (by omega)
  apply KummerLocalPrimaryUnit.pow_sub_one_mem_cube_of_local_pow (K := F)
    (Fact.out : p.Prime) hp5 (ramifiedPlace hζ) u
    (unit_pow_sub_one_mem_ramifiedIdeal hζ u)
    (natCast_mem_ramifiedIdeal_pow hζ 2 (by omega))
  exact (mk_mem_localPowerSpace_iff p u).mp hloc (ramifiedPlace hζ) hpv

end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence
