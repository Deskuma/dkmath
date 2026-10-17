/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicIdealBridge
import DkMath.Lib.NumberTheory.CosmicRamification

#print "file: DkMath.Lib.NumberTheory.CosmicRamifiedIdealPower"

/-!
# 分岐因子を剥離した後のイデアル冪配分

`αᵢ = x + (1-ζ^i)u`、`λ = ζ-1` とする。前段の一段剥離は
`αᵢ=λβᵢ` と `λ∤βᵢ` を与えた。このファイルは、元の積が p 乗なら
`(βᵢ)=Iᵢ^p` となることを証明する。類群条件はまだ使用しない。

鍵は、`(βᵢ)` と `((λ) * ∏ⱼ≠ᵢ (αⱼ))` の互いに素性である。
共通素イデアルは既存の support 解析によって λ を含む。一方、
非零素イデアル `(λ)` は Dedekind 整域では極大なので、その共通素イデアルは
`(λ)` 自身でなければならず、`λ∤βᵢ` と矛盾する。

自明因子 x に残る λ の冪も残余積へ含める。このため、各 βᵢ の冪抽出には
全体の分岐指数を先に計算する必要がない。指数の合同条件や降下の構成は
この結果とは別の段階である。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField
open DkMath.CosmicFormula

private theorem not_mem_prime_of_maximal_span
    {R : Type*} [CommRing R] {ell β : R}
    (hmax : (Ideal.span ({ell} : Set R)).IsMaximal) (hβ : ¬ ell ∣ β)
    {P : Ideal R} (hP : P.IsPrime) (hramP : ell ∈ P) (hβP : β ∈ P) : False := by
  have hle : Ideal.span ({ell} : Set R) ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hramP
  have heq : Ideal.span ({ell} : Set R) = P := hmax.eq_of_le hP.ne_top hle
  apply hβ
  exact Ideal.mem_span_singleton.mp (heq.symm ▸ hβP)

/-- 極大な主イデアルを生成する λ を含まない元は、`(λ)` と互いに素。
ここでの互いに素性は元の gcd ではなく、イデアルの comaximal 性である。 -/
theorem stripped_span_isCoprime_ramifier
    {R : Type*} [CommRing R] {ell β : R}
    (hmax : (Ideal.span ({ell} : Set R)).IsMaximal) (hβ : ¬ ell ∣ β) :
    IsCoprime (Ideal.span ({β} : Set R)) (Ideal.span ({ell} : Set R)) := by
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hβP hramP hP
  exact not_mem_prime_of_maximal_span hmax hβ hP
    (hramP (Ideal.mem_span_singleton_self _)) (hβP (Ideal.mem_span_singleton_self _))

/-- 剥離後の商のイデアルと、異なる元の phase factor のイデアルは互いに素。
原始性により共通素イデアルは λ を含み、極大性と `λ∤β` がそれを排除する。 -/
theorem stripped_phase_span_isCoprime_other
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u β : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hxu : IsCoprime x u) (hmax : (Ideal.span ({ζ - 1} : Set R)).IsMaximal)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j)
    (hstrip : x + (1 - ζ ^ i) * u = (ζ - 1) * β) (hβ : ¬ ζ - 1 ∣ β) :
    IsCoprime (Ideal.span ({β} : Set R))
      (Ideal.span ({x + (1 - ζ ^ j) * u} : Set R)) := by
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hleβ hlej hP
  have hβP := hleβ (Ideal.mem_span_singleton_self _)
  have hfi : x + (1 - ζ ^ i) * u ∈ P := by
    rw [hstrip]
    exact P.mul_mem_left _ hβP
  have hfj := hlej (Ideal.mem_span_singleton_self _)
  have hramP := common_prime_contains_ramified hp hζ hxu hi hj hij hP hfi hfj
  exact not_mem_prime_of_maximal_span hmax hβ hP hramP hβP

/-- 一段剥離した phase factor の主イデアルは p 乗である。

`x*GN=c^p` から元の全因子積を作り、chosen factor の λ を残余積へ移す。
商のイデアルは λ と他の全因子の両方に互いに素なので、Dedekind 整域の
冪抽出を適用できる。非零なイデアル根を返し、類群や単元はまだ使わない。 -/
theorem exists_ideal_pow_of_stripped_phaseFactor
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : ℕ} {ζ x u c β : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hramPrime : Prime (ζ - 1)) (hxu : IsCoprime x u)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p)
    {i : ℕ} (hi : i < p)
    (hstrip : x + (1 - ζ ^ i) * u = (ζ - 1) * β) (hβ : ¬ ζ - 1 ∣ β) :
    ∃ I : Ideal R, I ≠ ⊥ ∧ Ideal.span ({β} : Set R) = I ^ p := by
  classical
  have hmax : (Ideal.span ({ζ - 1} : Set R)).IsMaximal :=
    (Ideal.isPrime_span_singleton_of_prime hramPrime).isMaximal
      (by
        intro h
        exact hramPrime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  have hcopRam := stripped_span_isCoprime_ramifier hmax hβ
  have hcoprest : IsCoprime (Ideal.span ({β} : Set R))
      (∏ j ∈ (Finset.range p).erase i, Ideal.span ({x + (1 - ζ ^ j) * u} : Set R)) := by
    apply IsCoprime.prod_right
    intro j hj
    exact stripped_phase_span_isCoprime_other hp hζ hxu hmax hi
      (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)
      (Finset.mem_erase.mp hj).1.symm hstrip hβ
  have hm : Ideal.span ({β} : Set R) *
      (Ideal.span ({ζ - 1} : Set R) *
        ∏ j ∈ (Finset.range p).erase i, Ideal.span ({x + (1 - ζ ^ j) * u} : Set R)) =
      Ideal.span ({c} : Set R) ^ p := by
    calc
      _ = (Ideal.span ({ζ - 1} : Set R) * Ideal.span ({β} : Set R)) *
          ∏ j ∈ (Finset.range p).erase i, Ideal.span ({x + (1 - ζ ^ j) * u} : Set R) := by
        ac_rfl
      _ = Ideal.span ({x + (1 - ζ ^ i) * u} : Set R) *
          ∏ j ∈ (Finset.range p).erase i, Ideal.span ({x + (1 - ζ ^ j) * u} : Set R) := by
        rw [Ideal.span_singleton_mul_span_singleton, ← hstrip]
      _ = ∏ j ∈ Finset.range p, Ideal.span ({x + (1 - ζ ^ j) * u} : Set R) :=
        Finset.mul_prod_erase (Finset.range p)
          (fun j : ℕ => Ideal.span ({x + (1 - ζ ^ j) * u} : Set R)) (Finset.mem_range.mpr hi)
      _ = _ := prod_phase_span_eq_span_pow hp.pos hζ heq
  obtain ⟨I, hI⟩ := exists_eq_pow_of_isCoprime_mul_eq_pow (hcopRam.mul_right hcoprest) hm
  refine ⟨I, ?_, hI⟩
  intro hz
  have hc0 : Ideal.span ({c} : Set R) ≠ ⊥ := by
    intro h
    exact hc (Ideal.span_singleton_eq_bot.mp h)
  rw [hI, hz, Ideal.bot_pow hp.ne_zero, Ideal.bot_mul] at hm
  exact (pow_ne_zero p hc0) hm.symm

/-- 整数座標の分岐側における、商の存在とイデアル p 乗配分の合成定理。

入力は `x*GN=c^p`、整数の原始性、`p∣x`、非零な c。
非自明な各因子について商 β と非零イデアル根 I を構成する。
`(αᵢ)=(λ)I^p` と `(β)=I^p` を両方保持する。
この段階では正則性を仮定せず、イデアル根が主イデアルとはまだ結論しない。 -/
theorem exists_ramified_phase_ideal_pow
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x u c : ℤ} (hxu : IsCoprime x u) (hx : (p : ℤ) ∣ x)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p)
    {i : ℕ} (hi0 : i ≠ 0) (hi : i < p) :
    ∃ (β : 𝓞 K) (I : Ideal (𝓞 K)),
      (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) = (hζ.toInteger - 1) * β ∧
      ¬ hζ.toInteger - 1 ∣ β ∧ I ≠ ⊥ ∧ Ideal.span ({β} : Set (𝓞 K)) = I ^ p ∧
      Ideal.span ({(x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K)} : Set (𝓞 K)) =
        Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) * I ^ p := by
  have hu : ¬ (p : ℤ) ∣ u := by
    intro hu
    obtain ⟨r, s, hrs⟩ := hxu
    have hp1 : (p : ℤ) ∣ 1 := by
      rw [← hrs]
      exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hu _)
    exact hp.out.not_dvd_one (by exact_mod_cast hp1)
  obtain ⟨β, hstrip, hβ⟩ := exists_ramified_phase_quotient_of_dvd_gap hζ hp3 hx hu hi0 hi
  have hcR : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc
  have heqR : (x : 𝓞 K) * GTail p 1 (x : 𝓞 K) (u : 𝓞 K) = (c : 𝓞 K) ^ p := by
    have h := congrArg (fun n : ℤ => (n : 𝓞 K)) heq
    simpa [GTail] using h
  obtain ⟨I, hI0, hI⟩ := exists_ideal_pow_of_stripped_phaseFactor hp.out
    hζ.toInteger_isPrimitiveRoot hζ.zeta_sub_one_prime' (hxu.map (Int.castRingHom (𝓞 K)))
    hcR heqR hi hstrip hβ
  refine ⟨β, I, hstrip, hβ, hI0, hI, ?_⟩
  rw [hstrip, ← Ideal.span_singleton_mul_span_singleton, hI]

/-- 各非自明因子の `(αᵢ)=(λ)Iᵢ^p` を GN 全体の主イデアル等式へ束ねる。
因子数 p-1 が λ の指数となり、イデアル根の積の p 乗を取り出す。 -/
theorem span_GTail_eq_ramifier_pow_mul_roots_pow
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ : R} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (x u : R)
    (I : ℕ → Ideal R)
    (hI : ∀ i ∈ (Finset.range p).erase 0,
      Ideal.span ({x + (1 - ζ ^ i) * u} : Set R) =
        Ideal.span ({ζ - 1} : Set R) * I i ^ p) :
    Ideal.span ({GTail p 1 x u} : Set R) =
      Ideal.span ({ζ - 1} : Set R) ^ (p - 1) *
        (∏ i ∈ (Finset.range p).erase 0, I i) ^ p := by
  classical
  rw [span_GTail_eq_prod_phase_span hp hζ]
  calc
    _ = ∏ i ∈ (Finset.range p).erase 0, Ideal.span ({ζ - 1} : Set R) * I i ^ p := by
      apply Finset.prod_congr rfl
      exact hI
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_range.mpr hp), Finset.card_range, Finset.prod_pow]

/-- 全非自明因子の商とイデアル根を同時に選び、分岐冪の配分を記録する。

`(GN)=(λ)^(p-1)(∏Iᵢ)^p` と
`(x)(λ)^(p-1)(∏Iᵢ)^p=(c)^p` を返すので、自明因子 x の余分な分岐冪も
式の中に残る。ここでは x の λ 進指数を具体的な自然数へ変換しない。
添字範囲外の β, I の値には数学的な主張を課さない。 -/
theorem exists_ramified_ideal_power_family
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x u c : ℤ} (hxu : IsCoprime x u) (hx : (p : ℤ) ∣ x)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p) :
    ∃ (β : ℕ → 𝓞 K) (I : ℕ → Ideal (𝓞 K)),
      (∀ i ∈ (Finset.range p).erase 0,
        (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) = (hζ.toInteger - 1) * β i ∧
        ¬ hζ.toInteger - 1 ∣ β i ∧ I i ≠ ⊥ ∧ Ideal.span ({β i} : Set (𝓞 K)) = I i ^ p) ∧
      Ideal.span ({GTail p 1 (x : 𝓞 K) (u : 𝓞 K)} : Set (𝓞 K)) =
        Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) ^ (p - 1) *
          (∏ i ∈ (Finset.range p).erase 0, I i) ^ p ∧
      Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) *
          Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) ^ (p - 1) *
          (∏ i ∈ (Finset.range p).erase 0, I i) ^ p =
        Ideal.span ({(c : 𝓞 K)} : Set (𝓞 K)) ^ p := by
  classical
  have hex (i : ℕ) : ∃ (β : 𝓞 K) (I : Ideal (𝓞 K)), i ∈ (Finset.range p).erase 0 →
      (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) = (hζ.toInteger - 1) * β ∧
      ¬ hζ.toInteger - 1 ∣ β ∧ I ≠ ⊥ ∧ Ideal.span ({β} : Set (𝓞 K)) = I ^ p := by
    by_cases hi : i ∈ (Finset.range p).erase 0
    · obtain ⟨β, I, hstrip, hβ, hI0, hI, _⟩ := exists_ramified_phase_ideal_pow hζ hp3 hxu hx hc heq
        (Finset.mem_erase.mp hi).1 (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
      exact ⟨β, I, fun _ => ⟨hstrip, hβ, hI0, hI⟩⟩
    · exact ⟨0, ⊥, fun h => (hi h).elim⟩
  choose β I hdata using hex
  have hledger := span_GTail_eq_ramifier_pow_mul_roots_pow hp.out.pos
    hζ.toInteger_isPrimitiveRoot (x : 𝓞 K) (u : 𝓞 K) I (by
      intro i hi
      obtain ⟨hstrip, _, _, hI⟩ := hdata i hi
      rw [hstrip, ← Ideal.span_singleton_mul_span_singleton, hI])
  refine ⟨β, I, hdata, hledger, ?_⟩
  have heqR : (x : 𝓞 K) * GTail p 1 (x : 𝓞 K) (u : 𝓞 K) = (c : 𝓞 K) ^ p := by
    have h := congrArg (fun n : ℤ => (n : 𝓞 K)) heq
    simpa [GTail] using h
  rw [mul_assoc, ← hledger, Ideal.span_singleton_mul_span_singleton, heqR,
    Ideal.span_singleton_pow]

/-- 全体の分岐因子を `(p)` にまとめた GN のイデアル p 乗表示。
非零イデアル J に対して `(GN)=(p)J^p` を得る。
`(x)(p)J^p=(c)^p` も保持し、例外因子 x を消去しない。
J の主イデアル性や、単元の合同条件はこの定理の結論に含まれない。 -/
theorem exists_ramified_GTail_ideal_pow
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x u c : ℤ} (hxu : IsCoprime x u) (hx : (p : ℤ) ∣ x)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p) :
    ∃ J : Ideal (𝓞 K), J ≠ ⊥ ∧
      Ideal.span ({GTail p 1 (x : 𝓞 K) (u : 𝓞 K)} : Set (𝓞 K)) =
        Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) * J ^ p ∧
      Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) *
          Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) * J ^ p =
        Ideal.span ({(c : 𝓞 K)} : Set (𝓞 K)) ^ p := by
  classical
  obtain ⟨β, I, hdata, hledger, hfull⟩ :=
    exists_ramified_ideal_power_family hζ hp3 hxu hx hc heq
  refine ⟨∏ i ∈ (Finset.range p).erase 0, I i, ?_, ?_, ?_⟩
  · change (∏ i ∈ (Finset.range p).erase 0, I i) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (hdata i hi).2.2.1
  · simpa only [ramifiedIdeal_pow_eq_prime_span hζ] using hledger
  · simpa only [ramifiedIdeal_pow_eq_prime_span hζ] using hfull

end DkMath.Lib.NumberTheory
