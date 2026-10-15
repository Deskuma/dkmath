/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedIdealPower
import DkMath.Lib.NumberTheory.CosmicRamifiedValuation
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# 分岐イデアル冪と整数付値を保存するパケット

λ は `hζ.toInteger-1`、αᵢ は `x+(1-ζ^i)u` と固定する。これらを別々に
自由なデータとして入力せず、同じ座標から派生させる。βᵢ と Iᵢ の選択、
積 J、GN の主イデアル等式、整数の先頭補正、付値配分を一つに保持する。

基底パケットは正則性なしで構成する。類群条件を与えたときだけ、**同じ**
Iᵢ の生成元と βᵢ の単元倍 p 乗表示を追加する。いずれも次の解や減少性を
フィールドとして仮定せず、降下定理とは区別する。
-/

open scoped BigOperators NumberField nonZeroDivisors
open DkMath.CosmicFormula

namespace DkMath.Lib.NumberTheory

/-- 正則性を使わずに構成できる分岐側の保存データ。
添字の主張は `1,...,p-1` のみ。範囲外の関数値に数学的意味を課さない。 -/
structure RamifiedIdealPowerPacket
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u c : ℤ) where
  prime_ge_three : 3 ≤ p
  primitive : IsCoprime x u
  gap_divisible : (p : ℤ) ∣ x
  parameter_not_divisible : ¬ (p : ℤ) ∣ u
  right_nonzero : c ≠ 0
  product_eq : x * GTail p 1 x u = c ^ p
  quotient : ℕ → 𝓞 K
  idealRoot : ℕ → Ideal (𝓞 K)
  factor : ∀ i ∈ (Finset.range p).erase 0,
    (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) = (hζ.toInteger - 1) * quotient i ∧
    ¬ hζ.toInteger - 1 ∣ quotient i ∧ idealRoot i ≠ ⊥ ∧
    Ideal.span ({quotient i} : Set (𝓞 K)) = idealRoot i ^ p
  gn_span : Ideal.span ({GTail p 1 (x : 𝓞 K) (u : 𝓞 K)} : Set (𝓞 K)) =
    Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) * (∏ i ∈ (Finset.range p).erase 0, idealRoot i) ^ p
  full_span : Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) *
    Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) * (∏ i ∈ (Finset.range p).erase 0, idealRoot i) ^ p =
    Ideal.span ({(c : 𝓞 K)} : Set (𝓞 K)) ^ p
  headCorrection : ℤ
  head_eq : GTail p 1 x u = (p : ℤ) * u ^ (p - 1) + (p : ℤ) ^ 2 * headCorrection
  gn_valuation : padicValInt p (GTail p 1 x u) = 1
  valuation_balance : padicValInt p x + 1 = p * padicValInt p c

/-- パケットが保持する全イデアル根の積 J。独立の存在証人を選ばない。 -/
def RamifiedIdealPowerPacket.rootProduct
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) : Ideal (𝓞 K) :=
  ∏ i ∈ (Finset.range p).erase 0, P.idealRoot i

/-- 保存する J は非零。各因子の非零性を同じパケットから読む。 -/
theorem RamifiedIdealPowerPacket.rootProduct_ne_bot
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) : P.rootProduct ≠ ⊥ := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => (P.factor i hi).2.2.1)

/-- 既存の一段剥離と冪抽出を実行し、整数の付値情報まで格納する。
構造の定義だけでなく、入力からの inhabitance を証明する定理である。 -/
theorem nonempty_ramifiedIdealPowerPacket
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x u c : ℤ} (hxu : IsCoprime x u) (hx : (p : ℤ) ∣ x)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p) :
    Nonempty (RamifiedIdealPowerPacket hζ x u c) := by
  have hu : ¬ (p : ℤ) ∣ u := by
    intro hu
    obtain ⟨r, s, hrs⟩ := hxu
    have hp1 : (p : ℤ) ∣ 1 := by
      rw [← hrs]
      exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hu _)
    exact hp.out.not_dvd_one (by exact_mod_cast hp1)
  obtain ⟨β, I, hdata, hgn, hfull⟩ := exists_ramified_ideal_power_family hζ hp3 hxu hx hc heq
  obtain ⟨M, hM⟩ := integral_GN_eq_head_add_prime_sq_mul hp.out hp3 hx (u := u)
  exact ⟨{
    prime_ge_three := hp3
    primitive := hxu
    gap_divisible := hx
    parameter_not_divisible := hu
    right_nonzero := hc
    product_eq := heq
    quotient := β
    idealRoot := I
    factor := hdata
    gn_span := by simpa only [ramifiedIdeal_pow_eq_prime_span hζ] using hgn
    full_span := by simpa only [ramifiedIdeal_pow_eq_prime_span hζ] using hfull
    headCorrection := M
    head_eq := hM
    gn_valuation := padicValInt_GN_eq_one_of_dvd_gap hp3 hx hu
    valuation_balance := padicValInt_gap_add_one_eq_prime_mul hp3 hx hu hc heq }⟩

/-- 類群条件を与えた後の拡張。基底の βᵢ, Iᵢ を変更せず、単元と生成元を追加する。
単元は整数ノルムで符号に落とせるが、この構造内では消去しない。 -/
structure RamifiedPrincipalPowerPacket
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u c : ℤ)
    extends RamifiedIdealPowerPacket hζ x u c where
  unitFactor : ℕ → 𝓞 K
  generator : ℕ → 𝓞 K
  principal : ∀ i ∈ (Finset.range p).erase 0,
    IsUnit (unitFactor i) ∧ Ideal.span ({generator i} : Set (𝓞 K)) = idealRoot i ∧
    quotient i = unitFactor i * generator i ^ p

/-- 正則性による拡張は既存パケットの同じイデアル根を主イデアル化する。
返した拡張の射影が入力パケットと等しいことも明示する。 -/
theorem RamifiedIdealPowerPacket.exists_principal_extension
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ x u c, Q.toRamifiedIdealPowerPacket = P := by
  classical
  have hex (i : ℕ) : ∃ ε γ : 𝓞 K, i ∈ (Finset.range p).erase 0 →
      IsUnit ε ∧ Ideal.span ({γ} : Set (𝓞 K)) = P.idealRoot i ∧
      P.quotient i = ε * γ ^ p := by
    by_cases hi : i ∈ (Finset.range p).erase 0
    · obtain ⟨ε, γ, hε, hγ, hpow⟩ :=
        exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
          (mem_nonZeroDivisors_iff_ne_zero.mpr (P.factor i hi).2.2.1)
          (classGroupPTorsionFreeAt_of_coprime_card hreg) (P.factor i hi).2.2.2
      exact ⟨ε, γ, fun _ => ⟨hε, hγ, hpow⟩⟩
    · exact ⟨1, 0, fun h => (hi h).elim⟩
  choose ε γ hdata using hex
  exact ⟨{
    toRamifiedIdealPowerPacket := P
    unitFactor := ε
    generator := γ
    principal := hdata }, rfl⟩

/-- 剥離した円分因子の単元倍 p 乗表示を、厳密な整数 `GN=p*t^p` へ戻す。
N(λ)=+p と N(ε)=±1 を使い、奇数冪の根に符号を吸収する。
円分整数環の ε が p 乗であることは仮定も結論もしない。 -/
theorem exists_integral_GTail_eq_prime_mul_pow_of_ramified_factor
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {x u : ℤ} {ε γ : 𝓞 K} (hε : IsUnit ε)
    (hfactor : (x : 𝓞 K) + (1 - hζ.toInteger) * (u : 𝓞 K) =
      (hζ.toInteger - 1) * (ε * γ ^ p)) :
    ∃ t : ℤ, GTail p 1 x u = (p : ℤ) * t ^ p := by
  have hnorm := congrArg (Algebra.norm ℤ) hfactor
  rw [integral_norm_phaseFactor_eq_GTail hζ, map_mul, map_mul, map_pow,
    integral_norm_ramifier_eq_prime hζ hodd] at hnorm
  rcases Int.isUnit_iff.mp (hε.map (Algebra.norm ℤ)) with hpos | hneg
  · exact ⟨Algebra.norm ℤ γ, by simpa only [hpos, one_mul] using hnorm⟩
  · refine ⟨-Algebra.norm ℤ γ, ?_⟩
    simpa only [hneg, neg_one_mul, hodd.neg_pow] using hnorm

/-- 拡張パケットから chosen factor i=1 のノルムを読む。
整数根 t の p 非可除性も、基底パケットの exact-one 情報で保証する。
積等式を残し、x を消去したり次の FLT 解と見なしたりしない。 -/
theorem RamifiedPrincipalPowerPacket.exists_integral_root
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) :
    ∃ t : ℤ, GTail p 1 x u = (p : ℤ) * t ^ p ∧ ¬ (p : ℤ) ∣ t ∧
      x * ((p : ℤ) * t ^ p) = c ^ p := by
  have hi : 1 ∈ (Finset.range p).erase 0 := by
    exact Finset.mem_erase.mpr ⟨by decide, Finset.mem_range.mpr hp.out.one_lt⟩
  obtain ⟨hε, _, hpow⟩ := Q.principal 1 hi
  have hfactor := (Q.factor 1 hi).1
  rw [hpow] at hfactor
  obtain ⟨t, ht⟩ := exists_integral_GTail_eq_prime_mul_pow_of_ramified_factor hζ hodd hε
    (by simpa only [pow_one] using hfactor)
  refine ⟨t, ht, ?_, by rw [← ht]; exact Q.product_eq⟩
  intro hpt
  have hpow : (p : ℤ) ∣ t ^ p := hpt.trans (dvd_pow_self t hp.out.ne_zero)
  have hsq : (p : ℤ) ^ 2 ∣ GTail p 1 x u := by
    rw [ht, pow_two]
    exact mul_dvd_mul (dvd_refl (p : ℤ)) hpow
  exact (integral_GN_prime_dvd_and_not_sq hp.out Q.prime_ge_three
    Q.gap_divisible Q.parameter_not_divisible).2 hsq

end DkMath.Lib.NumberTheory
