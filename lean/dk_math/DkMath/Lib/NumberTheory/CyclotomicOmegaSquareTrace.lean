/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use DkMath SAME unitAction and omegaSquareProjector. Derive all-prime
unit-rank and primary-unit vanishing from actual fixed-place and finite-sum proofs.
-/

import DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace"

/-!
# 同じ ω² 射影子の trace=1 と、単元側の無条件消滅

指定された根と同じ無限素点の固定点数を代入し、有限体の重み付き和を計算する。
既存の同じ射影子の trace を1と証明して、従来の hrank/hunit を内部供給する。
類群・共鳴素点・巡回塔は本章では証明しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicInfinitePlaceFixed NumberFieldUnitLogTrace CyclotomicOmegaSquareUnitRank
open CyclotomicPrimaryUnitSpace KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- 有限体の単元上の非自明な冪和は零。 -/
theorem sum_units_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, (d : ZMod p) ^ i = 0 := by
  have h := FiniteField.sum_pow_units (ZMod p) i
  rw [ZMod.card p, ite_eq_right hi] at h
  simpa [Units.val_pow_eq_pow_val] using h

/-- 逆元による並べ替えを使った、逆冪の和の零化。 -/
theorem sum_units_inv_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ i)⁻¹ = 0 := by
  rw [← sum_units_pow_eq_zero (p := p) i hi]
  refine Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ fun d => ?_
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_pow]

/-- 射影子の trace の非指示関数項は相殺する。 -/
theorem sum_inv_sq_mul_sub_one (hp5 : 5 ≤ p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) = 0 := by
  have h1 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 1)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero (p := p) 1 (by intro h; have := Nat.le_of_dvd one_pos h; omega)
  have h2 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero (p := p) 2 (by intro h; have := Nat.le_of_dvd two_pos h; omega)
  have : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) =
      ((d : ZMod p) ^ 1)⁻¹ - ((d : ZMod p) ^ 2)⁻¹ := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := Units.ne_zero d
    field_simp
  simp only [this, Finset.sum_sub_distrib, h1, h2, sub_zero]

/-- d=±1 の2つの指示関数項は正確に2mを与える。 -/
theorem sum_inv_sq_mul_indicator (hp5 : 5 ≤ p) (m : ZMod p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) = 2 * m := by
  have : Fact (2 < p) := ⟨by omega⟩
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    simp only [Units.val_neg, Units.val_one] at this
    exact ZMod.neg_one_ne_one this
  have hsplit : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) =
      (if d = 1 then m else 0) + (if d = -1 then m else 0) := by
    intro d
    by_cases h1 : d = 1
    · subst h1; simp [hne.symm]
    · by_cases h2 : d = -1
      · subst h2; simp [hne]
      · simp [h1, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ既存 unitAction の具体的なトレース。 -/
theorem trace_unitAction (hp5 : 5 ≤ p) (d : (ZMod p)ˣ) :
    LinearMap.trace (ZMod p) _ (unitAction (p := p) ((characterEquiv hζ).symm d)) =
      ((d : ZMod p) - 1) +
        (if d = 1 ∨ d = -1 then (((p - 1) / 2 : ℕ) : ZMod p) else 0) := by
  rw [trace_unitAction_eq_character_add_fixedPlaces, card_fixedPlaces_prime hζ (by omega)]
  split_ifs <;> push_cast <;> ring

/-- 以前の同じ射影子の、同じ指標同型による有限和表示。新しく定義し直さない。 -/
theorem omegaSquareProjector_eq_units_sum :
    omegaSquareProjector hζ = (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ •
      ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ • unitAction (p := p) ((characterEquiv hζ).symm d) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, unitAction,
    MonoidHom.coe_mk, OneHom.coe_mk] using omegaSquareProjector_apply_units hζ x

/-- 実際の無限素点分類と有限体の和から、同じ射影子の trace=1 を証明する。 -/
theorem trace_omegaSquareProjector (hp5 : 5 ≤ p) :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1 := by
  have hm : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
    have h : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hc := congrArg (Nat.cast : ℕ → ZMod p) h
    push_cast at hc
    rw [hc, Nat.cast_sub hp.out.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [omegaSquareProjector_eq_units_sum, map_smul, map_sum]
  simp only [map_smul, trace_unitAction hζ hp5, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, sum_inv_sq_mul_sub_one hp5, sum_inv_sq_mul_indicator hp5,
    zero_add, hm, CyclotomicPrimaryLogNonzero.card_units_inv]
  ring

/-- 同じ実際の単元 ω² 固有空間の次元1。hrank/trace provider を要求しない。 -/
theorem weightSquareSpace_finrank_eq_one (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 :=
  weightSquareSpace_finrank_eq_one_of_trace hζ hp5 (trace_omegaSquareProjector hζ hp5)

/-- 同じ局所冪条件付き ω² 単元空間の無条件消滅。単元側の算術入力を解消する。 -/
theorem primaryWeightSquareSpace_eq_bot (hp5 : 5 ≤ p) : primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_trace hζ hp5 (trace_omegaSquareProjector hζ hp5)

/-- 同じ固有・局所冪条件を持つ実際の単元には、大域の整数環単元の p 乗根が存在する。 -/
theorem exists_global_unit_pow_of_primary (hp5 : 5 ≤ p) (u : (𝓞 (rootField ζ))ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ) :
    ∃ a : (𝓞 (rootField ζ))ˣ, a ^ p = u :=
  (primaryWeightSquareSpace_eq_bot_iff_global_power hζ).mp
    (primaryWeightSquareSpace_eq_bot hζ hp5) u hu

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace
