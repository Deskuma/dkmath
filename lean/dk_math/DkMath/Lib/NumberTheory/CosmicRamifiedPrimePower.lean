/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedQuadratic
import Mathlib.Data.Nat.Choose.Dvd

#print "file: DkMath.Lib.NumberTheory.CosmicRamifiedPrimePower"

/-!
# 保存パケットから mod λ^p の単元合同へ

λ=ζ−1 とおく。p²∣x は λ^(2(p−1))∣x を与えるので、p≥3 では λ^(p+1)∣x。
剥離後に残るのは幾何和全体 Sᵢ であり、係数を次数ごとに展開する必要はない。
また γ≡1 mod λ の p 乗は mod λ^p で1となる。
従って正規化単元は εᵢ≡−Sᵢ*u mod λ^p を満たす。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField

/-- 内部二項係数の p 可除性から一気に λ^p へ進む。
λ^(p−1)∣p, λ∣γ−1 なら λ^p∣γ^p−1。端項 k=p と内部項を分けて証明する。
円分体、単元性、完備化、無限級数は不要。 -/
theorem prime_power_dvd_pow_sub_one_of_dvd_pred_power
    {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) {ell γ : R}
    (hpRam : ell ^ (p - 1) ∣ (p : R)) (hγ : ell ∣ γ - 1) :
    ell ^ p ∣ γ ^ p - 1 := by
  obtain ⟨z, hz⟩ := hγ
  have hγeq : γ = ell * z + 1 := sub_eq_iff_eq_add.mp hz
  have hsum : γ ^ p - 1 =
      ∑ k ∈ Finset.range p, (Nat.choose p (k + 1) : R) * (ell * z) ^ (k + 1) := by
    rw [hγeq, add_pow, Finset.sum_range_succ']
    simp [mul_comm]
  rw [hsum]
  apply Finset.dvd_sum
  intro k hk
  have hklt : k + 1 ≤ p := by
    have hmem := Finset.mem_range.mp hk
    omega
  by_cases heq : k + 1 = p
  · rw [heq, Nat.choose_self, Nat.cast_one, one_mul, mul_pow]
    exact dvd_mul_right _ _
  · have hchoose : (p : R) ∣ (Nat.choose p (k + 1) : R) := by
      exact Nat.cast_dvd_cast (hp.dvd_choose_self (k := k + 1) (by omega) (by omega))
    have hcoeff := hpRam.trans hchoose
    have hpower : ell ∣ (ell * z) ^ (k + 1) :=
      (dvd_mul_right ell z).trans (dvd_pow_self _ (by omega))
    have hmul := mul_dvd_mul hcoeff hpower
    simpa only [← pow_succ, Nat.sub_add_cancel hp.one_le] using hmul

/-- 幾何和を展開せず、剥離式から mod λ^n の商の合同式を得る。
λ^(n+1)∣x の一段を取り消すので、ここだけ非零な λ と整域を要求する。 -/
theorem stripped_phaseFactor_geom_sum_dvd_pow
    {R : Type*} [CommRing R] [IsDomain R]
    {ζ x u β : R} (hRam : ζ - 1 ≠ 0) (n i : ℕ) (hx : (ζ - 1) ^ (n + 1) ∣ x)
    (hstrip : x + (1 - ζ ^ i) * u = (ζ - 1) * β) :
    (ζ - 1) ^ n ∣ β + (∑ k ∈ Finset.range i, ζ ^ k) * u := by
  have hprod : (ζ - 1) * (β + (∑ k ∈ Finset.range i, ζ ^ k) * u) = x := by
    rw [mul_add, ← mul_assoc, mul_geom_sum, ← hstrip]
    ring
  obtain ⟨q, hq⟩ := hx
  exact ⟨q, mul_left_cancel₀ hRam (by rw [hprod, hq, pow_succ']; ring)⟩

/-- パケットが持つ p²∣x は、剥離後に mod λ^p を読むための深度を供給する。
p=3 では境界 2(p−1)=p+1 が等号で成立する。 -/
theorem RamifiedIdealPowerPacket.ramifier_pow_succ_dvd_gap
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) :
    (hζ.toInteger - 1) ^ (p + 1) ∣ (x : 𝓞 K) := by
  have hpSq : (p : 𝓞 K) ^ 2 ∣ (x : 𝓞 K) := by
    obtain ⟨q, hq⟩ := P.prime_sq_dvd_gap
    exact ⟨(q : 𝓞 K), by exact_mod_cast hq⟩
  have hpow : (hζ.toInteger - 1) ^ ((p - 1) * 2) ∣ (p : 𝓞 K) ^ 2 := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd
      (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd 2
  have hbound : p + 1 ≤ (p - 1) * 2 := by
    have hp3 := P.prime_ge_three
    omega
  exact (pow_dvd_pow (hζ.toInteger - 1) hbound).trans (hpow.trans hpSq)

/-- 剥離商は幾何和全体の −u 倍に mod λ^p で一致する。正則性は不要。 -/
theorem RamifiedIdealPowerPacket.quotient_geom_sum_dvd_pow_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    (hζ.toInteger - 1) ^ p ∣ P.quotient i +
      (∑ k ∈ Finset.range i, hζ.toInteger ^ k) * (u : 𝓞 K) :=
  stripped_phaseFactor_geom_sum_dvd_pow
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt) p i
    P.ramifier_pow_succ_dvd_gap (P.factor i hi).1

/-- 一次正規化した生成元の p 乗は mod λ^p で1。
ここで λ^(p−1)∣p と内部二項係数の p 可除性を合わせる。 -/
theorem ramifier_pow_prime_dvd_generator_pow_sub_one
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) {γ : 𝓞 K}
    (hγ : ramifiedReduction hζ hodd γ = 1) :
    (hζ.toInteger - 1) ^ p ∣ γ ^ p - 1 := by
  exact prime_power_dvd_pow_sub_one_of_dvd_pred_power hp.out
    (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd
    ((ramifiedReduction_eq_iff hζ hodd _ _).mp (by simpa only [map_one] using hγ))

/-- 正規化済みの同じ単元 ε と商 β が mod λ^p で一致する。 -/
theorem RamifiedPrincipalPowerPacket.unit_sub_quotient_dvd_pow_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ p ∣ Q.unitFactor i - Q.quotient i := by
  have hd := dvd_mul_of_dvd_left
    (dvd_neg.mpr (ramifier_pow_prime_dvd_generator_pow_sub_one hζ hodd hγ)) (Q.unitFactor i)
  convert hd using 1
  rw [(Q.principal i hi).2.2]
  ring

/-- GN の深度と生成元の p 乗合同を合わせ、ε≡−Sᵢ*u mod λ^p を得る。
既存の一次正規化だけでよく、新しい高次の正規化仮定は不要。 -/
theorem RamifiedPrincipalPowerPacket.unit_geom_sum_dvd_pow_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ p ∣ Q.unitFactor i +
      (∑ k ∈ Finset.range i, hζ.toInteger ^ k) * (u : 𝓞 K) := by
  have hd := Q.unit_sub_quotient_dvd_pow_prime hodd hi hγ
  have hq := Q.toRamifiedIdealPowerPacket.quotient_geom_sum_dvd_pow_prime hi
  convert dvd_add hd hq using 1
  ring

end DkMath.Lib.NumberTheory
