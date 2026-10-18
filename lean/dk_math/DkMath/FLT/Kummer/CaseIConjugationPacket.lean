/-
Adapted from leanprover-community/flt-regular, commit
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89,
FltRegular/NumberTheory/Cyclotomic/CaseI.lean.
Licensed under Apache-2.0; see DkMath/Lib/NumberTheory/RegularKummer/LICENSE.
DkMath changes: isolated namespace, Lean 4.34 compatibility, textbook commentary.
-/

module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

import DkMath.Lib.NumberTheory.RegularKummer.Cyclotomic.MoreLemmas
import DkMath.Lib.NumberTheory.RegularKummer.Cyclotomic.UnitConjugation

#print "file: DkMath.FLT.Kummer.CaseIConjugationPacket"

/-!
# Cyclotomic lemmas for Case I

単元倍 p 乗の線形因子から、共役比を介して整数 p で割れる4項式を作る。
CM 体の単元比は ζ の平方冪であり、p 乗とその共役は mod p で等しい。
最後に指数を `Fin p` に戻し、二つの負側位相が隣接する証拠を保持する。

この provider は整数反例や類数条件を仮定せず、因子表示だけを入力する。
GN の因子抽出との合成は `GNCaseIObstruction`、係数の排除原理は
`DkMath.Lib.NumberTheory.SparsePhaseObstruction` が担当する。
-/

@[expose] public section

section

open scoped NumberField nonZeroDivisors

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

open FractionalIdeal NumberField IsCMField

namespace DkMath.FLT.Kummer.CaseIConjugation

open DkMath.Lib.NumberTheory.RegularKummer

omit [NeZero p] in
/-- The difference between a `p`-th power and its complex conjugate is divisible by `p`. -/
theorem pow_sub_intGalConj_mem (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨a, γ, hγ⟩ := exists_dvd_pow_sub_Int_pow hp.ne' α
  rw [Ideal.mem_span_singleton]
  rw [sub_eq_iff_eq_add] at hγ
  rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_pow, map_intCast,
    add_sub_add_right_eq_sub, ← mul_sub]
  exact dvd_mul_right _ _

/-- Complex conjugation negates the exponent of the distinguished cyclotomic unit. -/
theorem exists_int_sum_eq_zero'_aux (x y i : ℤ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ringOfIntegersComplexConj K (x + y * ↑(zetaUnit ^ i) : 𝓞 K) =
      x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ) := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  ext
  simp only [map_add, map_intCast, map_mul, coe_ringOfIntegersComplexConj, zpow_neg, map_units_inv,
    add_right_inj, mul_eq_mul_left_iff, Int.cast_eq_zero]
  simp_rw [NumberField.Units.coe_zpow]
  left
  simp only [map_zpow₀]
  rw [← inv_zpow]
  congr
  change (complexConj K) ζ = ζ⁻¹
  exact complexConj_zeta hζ hp

/-- 単元倍 p 乗の因子から整数 p で割れる4項式を作る。
共役比を ζ の平方冪で表し、α^p とその共役が mod p で等しいことを使う。 -/
theorem exists_int_sum_eq_zero' (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hroot⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux _ _ _ _ hp, h, ← hroot, Units.val_mul, mul_assoc,
    ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u (pow_sub_intGalConj_mem α hp) using 3
  ext
  simp only [map_mul, map_pow, map_units_inv, Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv,
    RingOfIntegers.mapRingEquiv_apply, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    coe_ringOfIntegersComplexConj, ne_eq, EmbeddingLike.map_eq_zero_iff,
    FaithfulSMul.algebraMap_eq_zero_iff, Units.ne_zero, not_false_eq_true, inv_mul_cancel_left₀]

/-- An integer exponent giving the Case I complex-conjugation congruence modulo `p`. -/
theorem exists_int_sum_eq_zero (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ x y i h hp
  refine ⟨k, ?_⟩
  have hz : ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) = (zetaUnit ^ (2 * (k : ℤ)) : (𝓞 K)ˣ) := by
    rw [← zpow_natCast (zetaUnit ^ k) 2, ← zpow_natCast zetaUnit k, ← zpow_mul]
    congr 1
    exact mul_comm _ _
  exact hz ▸ hk

end DkMath.FLT.Kummer.CaseIConjugation

end

namespace DkMath.FLT.Kummer.CaseIConjugation

open scoped NumberField
open Int Ideal

/-- 共役から得られる4項関係。位相の隣接条件と整数 p による可除性を
同じ packet に保持し、係数剛性への入口を明示する。 -/
structure Packet {p : ℕ} {K : Type*} [Field K] (ζ : 𝓞 K) (a b : ℤ) where
  k₁ : Fin p
  k₂ : Fin p
  adjacent : Int.ModEq p (k₂ : ℤ) ((k₁ : ℤ) - 1)
  divisible : (p : 𝓞 K) ∣ (a : 𝓞 K) + b * ζ - a * ζ ^ (k₁ : ℕ) - b * ζ ^ (k₂ : ℕ)

/-- 任意の素数次円分体で、単元倍 p 乗の因子から隣接する二位相を得る。
指数を p の剰余へ戻すので、負の共役指数も `Fin p` に収まる。
この段階では FLT 方程式も類群条件も仮定しない。 -/
theorem exists_adjacent_phases
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hp5 : 5 ≤ p)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) {a b : ℤ}
    {u : (𝓞 K)ˣ} {α : 𝓞 K} (hfactor : (u : 𝓞 K) * α ^ p = a + ζ * b) :
    ∃ k₁ k₂ : Fin p, Int.ModEq p (k₂ : ℤ) ((k₁ : ℤ) - 1) ∧
      (p : 𝓞 K) ∣ (a : 𝓞 K) + b * ζ - a * ζ ^ (k₁ : ℕ) - b * ζ ^ (k₂ : ℕ) := by
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let zetaUnit := (hζ'.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have h : ζ = (zetaUnit : 𝓞 K) := by rfl
  have hP : p ≠ 2 := by omega
  have hu := hfactor
  rw [h, mul_comm _ (↑b : 𝓞 K), ← pow_one zetaUnit] at hu
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero hζ' a b 1 hu.symm (by omega)
  simp only [zpow_one, zpow_neg, mem_span_singleton] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by simp [(Fact.out : p.Prime).ne_zero]
  have hζ_map : (algebraMap (𝓞 K) K) ζ = ζ' := rfl
  refine ⟨⟨(2 * k % p).natAbs, ?_⟩, ⟨((2 * k - 1) % p).natAbs, ?_⟩, ?_, ?_⟩
  repeat'
    rw [← natAbs_natCast p]
    refine natAbs_lt_natAbs_of_nonneg_of_lt (emod_nonneg _ hpcoe) ?_
    rw [natAbs_natCast]
    exact emod_lt_of_pos _ (by simp [(Fact.out : p.Prime).pos])
  · simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_eq_intCast_iff,
      ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, Int.cast_one]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert! hk using 3
  rw [mul_add, mul_comm (↑a : 𝓞 K), ← mul_assoc _ (↑b : 𝓞 K), mul_comm _ (↑b : 𝓞 K),
    mul_assoc (↑b : 𝓞 K)]
  congr 2
  · ext
    simp only [map_pow, NumberField.Units.coe_zpow, hζ_map]
    change ζ' ^ ↑(2 * k % ↑p).natAbs = ζ' ^ (2 * k)
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub₀ (hζ'.ne_zero (Fact.out : p.Prime).ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, sub_self]
  · ext
    simp only [map_pow, _root_.map_mul, NumberField.Units.coe_zpow, map_units_inv, hζ_map]
    change ζ' ^ ↑((2 * k - 1) % ↑p).natAbs = ζ' ^ (2 * k) * ζ'⁻¹
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub_one₀ (hζ'.ne_zero (Fact.out : p.Prime).ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero (Fact.out : p.Prime).ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, Int.cast_one, sub_self]

/-- 存在証明を packet に包む。選ばれた位相と可除性の証明を一緒に運ぶ。 -/
theorem packet_of_factor
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hp5 : 5 ≤ p)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) {a b : ℤ}
    {u : (𝓞 K)ˣ} {α : 𝓞 K} (hfactor : (u : 𝓞 K) * α ^ p = a + ζ * b) :
    Nonempty (Packet (p := p) ζ a b) := by
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := exists_adjacent_phases hp5 hζ hfactor
  exact ⟨⟨k₁, k₂, hcong, hdiv⟩⟩

end DkMath.FLT.Kummer.CaseIConjugation
