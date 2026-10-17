/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedPrimary
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

#print "file: DkMath.FLT.Kummer.GNKummerUnitAdapter"

/-!
# Kummer 単元補題への適用境界

一般 p の `flt-regular` はこの Lake プロジェクトの依存に入っていない。
以下の命題型は、その外部定理を渡すための正確な契約であり、公理ではない。
一般の正則素数からこの契約を証明したとは数えない。

一方 p=3 では Mathlib の実際の単元補題から契約を証明できる。
その供給により、三次では未解析単元を残さない因子表示を実際に得る。
-/

namespace DkMath.FLT.Kummer

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory

/-- 外部の Kummer 単元補題が供給すべき命題。
単元群で、整数と mod p で合同な元が p 乗になるという**補題自体**の型である。
これを引数に取る後続定理は条件付きであり、正則性からの証明を置き換えない。 -/
def KummerUnitPowerCriterion (R : Type*) [CommRing R] (p : ℕ) : Prop :=
  ∀ δ : Rˣ, (∃ n : ℤ, (p : R) ∣ (δ : R) - (n : R)) → ∃ κ : Rˣ, δ = κ ^ p

/-- Mathlib の三次円分体版 Kummer 単元補題から、実際の供給を構成する。
mod 3 の整数合同を mod λ² に移し、δ=±1 を得る。±1 は自分自身の三乗である。
一般 p の単元補題を仮定する定理ではない。 -/
theorem cubic_kummer_unit_power_criterion
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    KummerUnitPowerCriterion (𝓞 K) 3 := by
  intro δ hcong
  have hcongRam : ∃ n : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (δ : 𝓞 K) - (n : 𝓞 K) := by
    obtain ⟨n, hn⟩ := hcong
    refine ⟨n, ?_⟩
    have hram : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) := by
      simpa using (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime 3 hζ).dvd
    exact hram.trans hn
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ δ hcongRam
    with hpos | hneg
  · exact ⟨1, by simpa only [one_pow] using hpos⟩
  · refine ⟨-1, ?_⟩
    rw [hneg]
    simp [pow_succ]

/-- Kummer 単元補題が供給されたとき、既存の δᵢ と同じ生成元から θᵢ を作る。
δᵢ=κᵢ^p を使い、λ*Sᵢ=ζ^i−1 と合わせて未解析単元のない因子表示を得る。
一般 p については明示した criterion 引数の下での条件付き定理。 -/
theorem factor_eq_zeta_sub_one_mul_pow_of_unit_criterion
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p)
    (hunit : KummerUnitPowerCriterion (𝓞 K) p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    ∃ θ : 𝓞 K, (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * θ ^ p := by
  obtain ⟨κ, hκ⟩ := hunit (Q.primaryUnit hi) ⟨-u, Q.primaryUnit_congruent_integer hodd hi hγ⟩
  have hκR := congrArg (fun v : (𝓞 K)ˣ => (v : 𝓞 K)) hκ
  simp only [Units.val_pow_eq_pow_val] at hκR
  refine ⟨(κ : 𝓞 K) * Q.generator i, ?_⟩
  rw [(Q.primaryUnit_spec hodd hi hγ).2.2, hκR, mul_pow]

/-- FLT 座標への条件付き adapter。外部の単元補題を引数として渡す箇所を明示する。
類数条件だけでこの endpoint を無条件に得たという主張ではない。 -/
theorem exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    (hunit : KummerUnitPowerCriterion (𝓞 K) p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    ∃ θ : 𝓞 K, (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * θ ^ p := by
  obtain ⟨Q, hdata⟩ := exists_GN_ramified_primary_packet hζ hodd hp3 hc0 heq hprim hcase hreg
  obtain ⟨θ, hθ⟩ := factor_eq_zeta_sub_one_mul_pow_of_unit_criterion Q hodd hunit hi (hdata i hi).1
  refine ⟨θ, ?_⟩
  convert hθ using 1
  push_cast
  ring

/-- 三次では外部 criterion 引数なしで単元を除去する。
Mathlib の三次単元補題を実際に適用した結果である。類数条件はイデアルの
主イデアル化に使い、無限降下や新しい FLT 解の存在は結論しない。 -/
theorem exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ 3 + b ^ 3 = c ^ 3)
    (hprim : IsCoprime a b) (hcase : (3 : ℤ) ∣ c)
    (hreg : Nat.Coprime 3 (Fintype.card (ClassGroup (𝓞 K)))) {i : ℕ}
    (hi : i ∈ (Finset.range 3).erase 0) :
    ∃ θ : 𝓞 K, (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * θ ^ 3 :=
  exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion hζ (by decide) (by decide)
    hc0 heq hprim hcase hreg (cubic_kummer_unit_power_criterion hζ) hi

end DkMath.FLT.Kummer
