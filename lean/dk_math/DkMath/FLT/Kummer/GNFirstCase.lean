/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNStructure
import DkMath.Lib.NumberTheory.CosmicRamification

/-!
# 標準 Case I 条件から GN の構造定理へ

教科書の非分岐条件は `p ∤ abc` である。Fermat の小定理によって
方程式を mod p に落とすと `a+b ≡ c` となるので、`p ∤ a+b` が従う。
これが前段の `IsCoprime (a+b) p` を供給する。

さらに円分因子の単元倍 p 乗表示に整数ノルムを適用する。
整数の単元は ±1 だけで、奇数冪には符号を吸収できるため、
GN 自身が整数の p 乗であるという必要条件が得られる。
円分整数環の単元そのものを p 乗とする主張とは区別する。
-/

open scoped NumberField
open DkMath.CosmicFormula

namespace DkMath.FLT.Kummer

/-- FLT 方程式を mod p に落とすと `a+b=c` になる。
各 p 乗を元自身に戻す Fermat の小定理だけを使う。 -/
theorem flt_gap_mod_prime
    {p : ℕ} [Fact p.Prime] {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) :
    ((a + b : ℤ) : ZMod p) = (c : ZMod p) := by
  have h := congrArg (fun n : ℤ => (n : ZMod p)) heq
  have hf (t : ZMod p) : t ^ p = t := by simp
  simpa only [Int.cast_add, Int.cast_pow, hf] using h

/-- `p ∤ c` と FLT 方程式から gap `a+b` の非分岐性が従う。
正則性や円分体は不要な、整数の合同式の段階である。 -/
theorem gap_isCoprime_prime_of_flt_equation
    {p : ℕ} [hp : Fact p.Prime] {a b c : ℤ}
    (heq : a ^ p + b ^ p = c ^ p) (hc : ¬ (p : ℤ) ∣ c) :
    IsCoprime (a + b) (p : ℤ) := by
  have hnot : ¬ (p : ℤ) ∣ a + b := by
    intro h
    apply hc
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp
    rw [← flt_gap_mod_prime heq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) p).mpr h
  exact ((Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.mpr hnot).symm

/-- **Case I の GN 版 Kummer 構造定理**。
標準条件 `p ∤ abc`、整数の原始性、類数との互いに素性から、
各因子 `a+ζ^i b` のイデアル根・生成元・単元倍 p 乗表示を構成する。
非分岐性や因子イデアルの冪性を別途入力する必要はない。 -/
theorem GN_kummer_structure_of_first_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {i : ℕ} (hi : i < p) :
    ∃ (I : Ideal (𝓞 K)) (ε γ : 𝓞 K), I ≠ ⊥ ∧
      Ideal.span ({(a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p ∧
      IsUnit ε ∧ Ideal.span ({γ} : Set (𝓞 K)) = I ∧
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) = ε * γ ^ p := by
  have hc : ¬ (p : ℤ) ∣ c := fun h => hfirst (dvd_mul_of_dvd_right h _)
  have hc0 : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
  exact GN_kummer_structure_of_regular hζ hodd hc0 heq hprim
    (gap_isCoprime_prime_of_flt_equation heq hc) hreg hi

/-- 単元倍 p 乗の円分因子から、GN の厳密な整数 p 乗表示を得る。
整数ノルムに落ちた単元は ±1。p が奇数なら負号を根へ移せる。
この処理は円分整数環の単元 sector を消したことにはならない。 -/
theorem exists_GN_eq_pow_of_kummerFactor_eq_unit_mul_pow
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {a b : ℤ} {ε γ : 𝓞 K} (hε : IsUnit ε)
    (hfactor : (a : 𝓞 K) + hζ.toInteger * (b : 𝓞 K) = ε * γ ^ p) :
    ∃ t : ℤ, GN p (a + b) (-b) = t ^ p := by
  have hnorm := congrArg (Algebra.norm ℤ) hfactor
  rw [norm_kummerFactor_eq_GN hζ, map_mul, map_pow] at hnorm
  have hunit : IsUnit (Algebra.norm ℤ ε) := hε.map (Algebra.norm ℤ)
  rcases Int.isUnit_iff.mp hunit with hpos | hneg
  · exact ⟨Algebra.norm ℤ γ, by simpa only [hpos, one_mul] using hnorm⟩
  · exact ⟨-Algebra.norm ℤ γ, by simpa only [hneg, neg_one_mul, hodd.neg_pow] using hnorm⟩

/-- Case I の原始的な仮想反例に対し、GN は整数の p 乗になる。
構造定理の chosen factor（i=1）へノルムを適用する必要条件であり、
GN が p 乗になれないという結論や FLT の矛盾を含まない。 -/
theorem exists_GN_eq_pow_of_first_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ t : ℤ, GN p (a + b) (-b) = t ^ p := by
  obtain ⟨I, ε, γ, _, _, hε, _, hfactor⟩ :=
    GN_kummer_structure_of_first_case hζ hodd heq hprim hfirst hreg hp.out.one_lt
  exact exists_GN_eq_pow_of_kummerFactor_eq_unit_mul_pow hζ hodd hε
    (by simpa only [pow_one] using hfactor)

end DkMath.FLT.Kummer
