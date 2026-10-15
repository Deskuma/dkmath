/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNFirstCase
import DkMath.Lib.NumberTheory.CosmicRamifiedIdealPower

/-!
# GN 版 Kummer 構造定理の分岐側

整数の原始的方程式 `a^p+b^p=c^p` を、p が c を割る向きで受け取る。
Fermat の小定理から p は gap `a+b` も割る。`x=a+b, u=-b` とすると、
前段の exact-one 剥離とイデアル冪配分が使える。

非自明な各因子について `(a+ζ^i b)=(ζ-1)I_i^p` を証明し、その後に
正則性を使って `a+ζ^i b=(ζ-1)ε_i γ_i^p` へ戻す。
自明因子 i=0 は余分な分岐冪を持つため、この主張には含めない。
任意の `p∣abc` からこの向きを選ぶ正規化、単元合同、無限降下は別の段階である。
-/

open scoped NumberField nonZeroDivisors
open DkMath.CosmicFormula DkMath.Lib.NumberTheory

namespace DkMath.FLT.Kummer

/-- p が c を割る向きの FLT 方程式では、p は gap `a+b` も割る。
Case I に用いた合同式と同じ `a+b≡c (mod p)` の分岐側である。 -/
theorem prime_dvd_gap_of_dvd_right_of_flt_equation
    {p : ℕ} [Fact p.Prime] {a b c : ℤ}
    (heq : a ^ p + b ^ p = c ^ p) (hc : (p : ℤ) ∣ c) :
    (p : ℤ) ∣ a + b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) p).mp
  rw [flt_gap_mod_prime heq]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hc

/-- **分岐側のイデアル冪配分定理**。

原始性、方程式、p≥3、p∣c から各非自明因子の商 β とイデアル根 I を構成する。
`λ∤β`、`(β)=I^p`、`(a+ζ^i b)=(λ)I^p` を同時に返す。
正則性を仮定しないので、イデアル分解の段階と類群の段階を区別できる。 -/
theorem GN_ideal_pow_of_ramified_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    {i : ℕ} (hi0 : i ≠ 0) (hi : i < p) :
    ∃ (β : 𝓞 K) (I : Ideal (𝓞 K)),
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) = (hζ.toInteger - 1) * β ∧
      ¬ hζ.toInteger - 1 ∣ β ∧ I ≠ ⊥ ∧ Ideal.span ({β} : Set (𝓞 K)) = I ^ p ∧
      Ideal.span ({(a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K)} : Set (𝓞 K)) =
        Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) * I ^ p := by
  have hxu : IsCoprime (a + b) (-b) := by
    simpa using (hprim.add_mul_left_left 1).neg_right
  have h := exists_ramified_phase_ideal_pow hζ hp3 hxu
    (prime_dvd_gap_of_dvd_right_of_flt_equation heq hcase) hc0
    ((signed_GN_identity hodd a b).trans heq) hi0 hi
  have hf : ((a + b : ℤ) : 𝓞 K) + (1 - hζ.toInteger ^ i) * ((-b : ℤ) : 𝓞 K) =
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) := by
    push_cast
    ring
  simpa only [hf] using h

/-- **GN 版 Kummer 構造定理（分岐側）**。

前定理のイデアル根を、類数と p の互いに素性で主イデアル化する。
各非自明因子の正確な λ 一段を保持して `a+ζ^i b=λ(εγ^p)` を得る。
単元 ε は残る。これを消す合同解析と降下は、この結論より後に必要になる。 -/
theorem GN_kummer_structure_of_ramified_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {i : ℕ} (hi0 : i ≠ 0) (hi : i < p) :
    ∃ (β : 𝓞 K) (I : Ideal (𝓞 K)) (ε γ : 𝓞 K),
      ¬ hζ.toInteger - 1 ∣ β ∧ I ≠ ⊥ ∧ Ideal.span ({β} : Set (𝓞 K)) = I ^ p ∧
      IsUnit ε ∧ Ideal.span ({γ} : Set (𝓞 K)) = I ∧ β = ε * γ ^ p ∧
      (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) = (hζ.toInteger - 1) * (ε * γ ^ p) := by
  obtain ⟨β, I, hstrip, hβ, hI0, hI, _⟩ :=
    GN_ideal_pow_of_ramified_case hζ hodd hp3 hc0 heq hprim hcase hi0 hi
  obtain ⟨ε, γ, hε, hγ, hpow⟩ :=
    exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI0)
      (classGroupPTorsionFreeAt_of_coprime_card hreg) hI
  exact ⟨β, I, ε, γ, hβ, hI0, hI, hε, hγ, hpow, by rw [hstrip, hpow]⟩

end DkMath.FLT.Kummer
