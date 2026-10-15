/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedUnitNormalization

/-!
# 剥離商と正規化単元の mod λ² 展開

λ=ζ−1 とおく。幾何和の次の係数 choose i 2 を追うと、λ³∣x のもとで
`βᵢ ≡ −i*u − choose i 2 * λ*u mod λ²` となる。
一般の分岐条件 p∣x だけでは p=3 の場合に λ³∣x を保証しない。
一方、既存の積と整数付値を持つパケットは p²∣x を与えるため、この境界を満たす。

生成元 γ≡1 mod λ を p 乗すると、λ∣p により γ^p≡1 mod λ² になる。
従って β=εγ^p の二次合同はそのまま ε に残る。単元の p 乗性や降下は主張しない。
-/

open scoped BigOperators NumberField

namespace DkMath.Lib.NumberTheory

/-- ζ^i を ζ=1 の周りで一次まで展開し、残りを (ζ−1)² で括る。
幾何和を使うので、二項係数の除算や体の仮定は不要。 -/
theorem sub_one_sq_dvd_pow_sub_linear
    {R : Type*} [CommRing R] (ζ : R) (i : ℕ) :
    (ζ - 1) ^ 2 ∣ ζ ^ i - 1 - (i : R) * (ζ - 1) := by
  obtain ⟨q, hq⟩ := sub_one_dvd_geom_sum_sub_nat ζ i
  refine ⟨q, ?_⟩
  calc
    _ = (ζ - 1) * ((∑ k ∈ Finset.range i, ζ ^ k) - (i : R)) := by
      symm
      rw [mul_sub, mul_geom_sum]
      ring
    _ = (ζ - 1) ^ 2 * q := by rw [hq]; ring

/-- 幾何和の mod λ² 展開。係数 Σ k<i k = choose i 2 は Pascal の漸化式で追う。
原始根、素数、整域はいずれも不要な有限多項式恒等式である。 -/
theorem sub_one_sq_dvd_geom_sum_sub_linear
    {R : Type*} [CommRing R] (ζ : R) (i : ℕ) :
    (ζ - 1) ^ 2 ∣ (∑ k ∈ Finset.range i, ζ ^ k) - (i : R) -
      (Nat.choose i 2 : R) * (ζ - 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hc : Nat.choose (i + 1) 2 = i + Nat.choose i 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ i 1
    rw [Finset.sum_range_succ, hc]
    push_cast
    convert dvd_add ih (sub_one_sq_dvd_pow_sub_linear ζ i) using 1
    ring

/-- λ を一つ剥がした商の二次合同式。剥離前には λ³∣x が必要である。
係数 choose i 2 は整数のまま保持し、2 の逆数を要求しない。 -/
theorem stripped_phaseFactor_quadratic_dvd
    {R : Type*} [CommRing R] [IsDomain R]
    {ζ x u β : R} (hRam : ζ - 1 ≠ 0) (hx : (ζ - 1) ^ 3 ∣ x) (i : ℕ)
    (hstrip : x + (1 - ζ ^ i) * u = (ζ - 1) * β) :
    (ζ - 1) ^ 2 ∣ β + (i : R) * u + (Nat.choose i 2 : R) * (ζ - 1) * u := by
  let S := ∑ k ∈ Finset.range i, ζ ^ k
  have hprod : (ζ - 1) * (β + S * u) = x := by
    rw [mul_add, ← mul_assoc, mul_geom_sum, ← hstrip]
    ring
  obtain ⟨q, hq⟩ := hx
  have hquot : β + S * u = (ζ - 1) ^ 2 * q :=
    mul_left_cancel₀ hRam (by rw [hprod, hq]; ring)
  have hd : (ζ - 1) ^ 2 ∣ β + S * u := ⟨q, hquot⟩
  have hs : (ζ - 1) ^ 2 ∣
      (S - (i : R) - (Nat.choose i 2 : R) * (ζ - 1)) * u :=
    dvd_mul_of_dvd_left (sub_one_sq_dvd_geom_sum_sub_linear ζ i) u
  convert dvd_sub hd hs using 1
  ring

/-- γ≡1 mod ell で ell∣n なら γ^n≡1 mod ell²。
一次項 n*(γ−1) が ell² に入り、高次項も平方因子を持つ。 -/
theorem square_dvd_pow_sub_one_of_dvd_natCast
    {R : Type*} [CommRing R] {ell γ : R} {n : ℕ}
    (hγ : ell ∣ γ - 1) (hn : ell ∣ (n : R)) :
    ell ^ 2 ∣ γ ^ n - 1 := by
  have hrem := (pow_dvd_pow_of_dvd hγ 2).trans (sub_one_sq_dvd_pow_sub_linear γ n)
  have hlin : ell ^ 2 ∣ (n : R) * (γ - 1) := by
    simpa only [pow_two] using mul_dvd_mul hn hγ
  simpa only [sub_add_cancel] using dvd_add hrem hlin

/-- β=εγ^n において正規化した γ の n 乗は二次まで消える。
ε の単元性自体はこの合同式には不要。 -/
theorem square_dvd_unit_sub_of_mul_pow
    {R : Type*} [CommRing R] {ell β ε γ : R} {n : ℕ}
    (hγ : ell ∣ γ - 1) (hn : ell ∣ (n : R)) (hpow : β = ε * γ ^ n) :
    ell ^ 2 ∣ ε - β := by
  have hd := dvd_mul_of_dvd_left
    (dvd_neg.mpr (square_dvd_pow_sub_one_of_dvd_natCast hγ hn)) ε
  convert hd using 1
  rw [hpow]
  ring

/-- mod ell² では、素元 ell の像は零でないが平方が零になる。
剰余一段の体とは異なり、二次剰余環に冪零元が現れることを明示する。 -/
theorem prime_class_mod_square_nonzero_nilpotent
    {R : Type*} [CommRing R] [IsDomain R] {ell : R} (h : Prime ell) :
    Ideal.Quotient.mk (Ideal.span ({ell ^ 2} : Set R)) ell ≠ 0 ∧
      (Ideal.Quotient.mk (Ideal.span ({ell ^ 2} : Set R)) ell) ^ 2 = 0 := by
  constructor
  · intro hz
    have hd : ell ^ 2 ∣ ell :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    obtain ⟨q, hq⟩ := hd
    have hq' : 1 = ell * q := mul_left_cancel₀ h.ne_zero (by
      simpa only [mul_one, pow_two, mul_assoc] using hq)
    exact h.not_isUnit (isUnit_of_dvd_one ⟨q, hq'⟩)
  · rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 二次分岐剰余環の大きさは p²。N(λ²)=N(λ)² と主イデアルの指数を使う。
元の数が p² でも、前定理の冪零元により体ではない。 -/
theorem card_ramifiedQuadraticResidue_eq_prime_sq
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    Nat.card (𝓞 K ⧸ Ideal.span ({(hζ.toInteger - 1) ^ 2} : Set (𝓞 K))) = p ^ 2 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    map_pow, integral_norm_ramifier_eq_prime hζ hodd]
  simp

/-- 既存の付値保存等式から、例外因子 x に少なくとも p² が含まれると分かる。
新しい非零条件や p∣c を入力せず、基底パケットの情報だけを使う。 -/
theorem RamifiedIdealPowerPacket.prime_sq_dvd_gap
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) : (p : ℤ) ^ 2 ∣ x := by
  have hbal := P.valuation_balance
  have hc : 1 ≤ padicValInt p c := by
    by_contra h
    have hz : padicValInt p c = 0 := by omega
    rw [hz, mul_zero] at hbal
    omega
  have hle : p ≤ p * padicValInt p c := by
    simpa only [mul_one] using Nat.mul_le_mul_left p hc
  have hx : 2 ≤ padicValInt p x := by
    have hp3 := P.prime_ge_three
    omega
  exact (padicValInt_dvd_iff 2 x).mpr (Or.inr hx)

/-- p²∣x と p∼λ^(p−1) を結び、二次の剥離合同に必要な λ³∣x を供給する。
p=3 の場合も整数の追加深度があるので含まれる。 -/
theorem RamifiedIdealPowerPacket.ramifier_cube_dvd_gap
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) :
    (hζ.toInteger - 1) ^ 3 ∣ (x : 𝓞 K) := by
  have hpSq : (p : 𝓞 K) ^ 2 ∣ (x : 𝓞 K) := by
    obtain ⟨q, hq⟩ := P.prime_sq_dvd_gap
    exact ⟨(q : 𝓞 K), by exact_mod_cast hq⟩
  have hramp := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
  have hpow : (hζ.toInteger - 1) ^ ((p - 1) * 2) ∣ (p : 𝓞 K) ^ 2 := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hramp.dvd 2
  have hbound : 3 ≤ (p - 1) * 2 := by
    have hp3 := P.prime_ge_three
    omega
  exact (pow_dvd_pow (hζ.toInteger - 1) hbound).trans (hpow.trans hpSq)

/-- 基底パケットの商の二次合同式。原始性・付値は既存パケットから供給され、
λ³∣x を追加で仮定する必要はない。 -/
theorem RamifiedIdealPowerPacket.quotient_quadratic_dvd
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    (hζ.toInteger - 1) ^ 2 ∣ P.quotient i + (i : 𝓞 K) * (u : 𝓞 K) +
      (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (u : 𝓞 K) :=
  stripped_phaseFactor_quadratic_dvd
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt)
    P.ramifier_cube_dvd_gap i (P.factor i hi).1

/-- γ≡1 mod λ と正規化したパケットでは、単元 ε と商 β は mod λ² で一致する。 -/
theorem RamifiedPrincipalPowerPacket.unit_sub_quotient_sq_dvd
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ 2 ∣ Q.unitFactor i - Q.quotient i := by
  have hγ' : hζ.toInteger - 1 ∣ Q.generator i - 1 :=
    (ramifiedReduction_eq_iff hζ hodd _ _).mp (by simpa only [map_one] using hγ)
  exact square_dvd_unit_sub_of_mul_pow hγ'
    (hζ.toInteger_isPrimitiveRoot.sub_one_dvd_natCast hp.out.one_lt) (Q.principal i hi).2.2

/-- 一次正規化済みの同じ生成元を使ったまま、単元の二次係数を読む。
`ε−β` と `β+i*u+choose i 2*λ*u` の可除性を加えるだけでよい。 -/
theorem RamifiedPrincipalPowerPacket.unitFactor_quadratic_dvd
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ 2 ∣ Q.unitFactor i + (i : 𝓞 K) * (u : 𝓞 K) +
      (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (u : 𝓞 K) := by
  have hdiff := Q.unit_sub_quotient_sq_dvd hodd hi hγ
  have hquot := Q.toRamifiedIdealPowerPacket.quotient_quadratic_dvd hi
  convert dvd_add hdiff hquot using 1
  ring

/-- 同じ基底パケットのまま生成元を正規化し、単元の二次係数 choose i 2 を固定する。
これは高次の単元解析の入力であり、単元の p 乗性の仮定を付け足す定理ではない。 -/
theorem RamifiedPrincipalPowerPacket.exists_quadratic_normalization
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) :
    ∃ Q' : RamifiedPrincipalPowerPacket hζ x u c,
      Q'.toRamifiedIdealPowerPacket = Q.toRamifiedIdealPowerPacket ∧
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q'.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q'.unitFactor i) = -(i : ZMod p) * (u : ZMod p) ∧
        (hζ.toInteger - 1) ^ 2 ∣ Q'.unitFactor i + (i : 𝓞 K) * (u : 𝓞 K) +
          (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (u : 𝓞 K) := by
  obtain ⟨Q', hbase, hred⟩ := Q.exists_residue_normalization hodd
  exact ⟨Q', hbase, fun i hi => ⟨(hred i hi).1, (hred i hi).2,
    Q'.unitFactor_quadratic_dvd hodd hi (hred i hi).1⟩⟩

end DkMath.Lib.NumberTheory
