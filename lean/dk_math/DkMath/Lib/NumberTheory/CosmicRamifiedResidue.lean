/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamification
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.Lib.NumberTheory.CosmicRamifiedResidue"

/-!
# 分岐剰余体と剥離商の一次合同式

λ=ζ−1 による剰余環は p 元を持ち、ZMod p と同型になる。
剥離前には全ての因子が x に潰れるが、λ を一つ除くと添字 i が現れる。
`αᵢ=λβᵢ`, `λ²∣x` から `βᵢ≡−i*u mod λ` を導く。
これは単元倍冪表示を読むための第一段であり、単元の p 乗性は主張しない。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField

/-- 幾何和は mod ζ−1 で項数 i に一致する。各 ζ^k−1 の可除性を足すだけなので、
原始根や素数性は不要。この幾何和が円分単元の剰余も計算する。 -/
theorem sub_one_dvd_geom_sum_sub_nat
    {R : Type*} [CommRing R] (ζ : R) (i : ℕ) :
    ζ - 1 ∣ (∑ k ∈ Finset.range i, ζ ^ k) - (i : R) := by
  have h : ζ - 1 ∣ ∑ k ∈ Finset.range i, (ζ ^ k - 1) := by
    apply Finset.dvd_sum
    intro k _
    simpa only [one_pow] using sub_dvd_pow_sub_pow ζ (1 : R) k
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] using h

/-- 分岐因子を一つ剥がすと、幾何和の項数が先頭係数となる。
`λ²∣x` のもとで `αᵢ=λβ` なら `λ∣β+i*u`。非零な λ による取消しを明示する。 -/
theorem stripped_phaseFactor_add_index_mul_dvd
    {R : Type*} [CommRing R] [IsDomain R]
    {ζ x u β : R} (hRam : ζ - 1 ≠ 0) (hx : (ζ - 1) ^ 2 ∣ x) (i : ℕ)
    (hstrip : x + (1 - ζ ^ i) * u = (ζ - 1) * β) :
    ζ - 1 ∣ β + (i : R) * u := by
  let S := ∑ k ∈ Finset.range i, ζ ^ k
  have hprod : (ζ - 1) * (β + S * u) = x := by
    rw [mul_add, ← mul_assoc, mul_geom_sum, ← hstrip]
    ring
  obtain ⟨q, hq⟩ := hx
  have hquot : β + S * u = (ζ - 1) * q :=
    mul_left_cancel₀ hRam (by rw [hprod, hq]; ring)
  have hd : ζ - 1 ∣ β + S * u := ⟨q, hquot⟩
  have hs : ζ - 1 ∣ (S - (i : R)) * u :=
    dvd_mul_of_dvd_left (sub_one_dvd_geom_sum_sub_nat ζ i) u
  convert dvd_sub hd hs using 1
  ring

/-- 分岐剰余環の元の数は p。整数ノルム N(ζ−1)=p を使い、
整数環の主イデアル指数と有限剰余体の大きさを接続する。 -/
theorem card_ramifiedResidue_eq_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    Nat.card (𝓞 K ⧸ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) = p := by
  rw [hζ.card_quotient_toInteger_sub_one, integral_norm_ramifier_eq_prime hζ hodd]
  simp

/-- 整数を保つ分岐剰余体の同型 `ZMod p ≃+* 𝓞 K/(ζ−1)`。
有限型の選択は実装内に閉じ込め、利用側に Fintype インスタンスを要求しない。 -/
noncomputable def ramifiedResidueEquiv
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    ZMod p ≃+* (𝓞 K ⧸ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) := by
  let := hζ.finite_quotient_toInteger_sub_one hp.out.one_lt
  let := Fintype.ofFinite (𝓞 K ⧸ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)))
  exact ZMod.ringEquivOfPrime _ hp.out (by
    rw [← Nat.card_eq_fintype_card, card_ramifiedResidue_eq_prime hζ hodd])

/-- 円分整数を `ζ↦1` で F_p に落とす環準同型。整数座標は通常の mod p 写像になる。 -/
noncomputable def ramifiedReduction
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) : 𝓞 K →+* ZMod p :=
  (ramifiedResidueEquiv hζ hodd).symm.toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))))

/-- reduction が零になることと、元が λ で割れることは同値。 -/
theorem ramifiedReduction_eq_zero_iff
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (a : 𝓞 K) :
    ramifiedReduction hζ hodd a = 0 ↔ hζ.toInteger - 1 ∣ a := by
  change (ramifiedResidueEquiv hζ hodd).symm
    (Ideal.Quotient.mk (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) a) = 0 ↔ _
  rw [map_eq_zero_iff _ (ramifiedResidueEquiv hζ hodd).symm.injective,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- 剰余の一致を、元の差の λ 可除性へ戻す。合同式と主イデアル所属を結ぶ API。 -/
theorem ramifiedReduction_eq_iff
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (a b : 𝓞 K) :
    ramifiedReduction hζ hodd a = ramifiedReduction hζ hodd b ↔
      hζ.toInteger - 1 ∣ a - b := by
  rw [← sub_eq_zero, ← map_sub, ramifiedReduction_eq_zero_iff]

/-- λ を零にするので、原始根 ζ の剰余は1。 -/
@[simp] theorem ramifiedReduction_zeta
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) :
    ramifiedReduction hζ hodd hζ.toInteger = 1 := by
  have h := (ramifiedReduction_eq_zero_iff hζ hodd (hζ.toInteger - 1)).mpr (dvd_refl _)
  simpa only [map_sub, map_one, sub_eq_zero] using h

/-- 素数分岐側の整数 x は λ² を含む。ここで初めて p≥3 が必要となる。 -/
theorem ramifier_sq_dvd_intCast_of_dvd_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x : ℤ} (hx : (p : ℤ) ∣ x) : (hζ.toInteger - 1) ^ 2 ∣ (x : 𝓞 K) := by
  have hxR : (p : 𝓞 K) ∣ (x : 𝓞 K) := by
    obtain ⟨q, hq⟩ := hx
    exact ⟨(q : 𝓞 K), by exact_mod_cast hq⟩
  exact (pow_dvd_pow (hζ.toInteger - 1) (by omega : 2 ≤ p - 1)).trans
    ((IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd.trans hxR)

/-- 剥離商の実際の剰余類。`βᵢ≡−i*u mod λ` を F_p の等式として返す。
正則性・イデアル冪性・単元倍冪表示はまだ使わない。 -/
theorem ramifiedReduction_stripped_phaseFactor
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {x u : ℤ} {β : 𝓞 K} (hx : (p : ℤ) ∣ x) (i : ℕ)
    (hstrip : (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) =
      (hζ.toInteger - 1) * β) :
    ramifiedReduction hζ hodd β = -(i : ZMod p) * (u : ZMod p) := by
  have hd := stripped_phaseFactor_add_index_mul_dvd
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt)
    (ramifier_sq_dvd_intCast_of_dvd_prime hζ hp3 hx) i hstrip
  have hz := (ramifiedReduction_eq_zero_iff hζ hodd _).mpr hd
  simp only [map_add, map_mul, map_natCast, map_intCast] at hz
  simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hz

/-- 幾何和で表した円分単元の剰余は添字 i。 -/
@[simp] theorem ramifiedReduction_geom_sum
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (i : ℕ) :
    ramifiedReduction hζ hodd (∑ k ∈ Finset.range i, hζ.toInteger ^ k) = (i : ZMod p) := by
  simp

/-- F_p の任意の非零剰余は、円分整数環の **大域的な単元** に持ち上がる。
非零剰余の代表 i に対し、幾何和 1+ζ+...+ζ^(i−1) を選ぶ。
単元群の p 乗写像が全射だという仮定は使わない。 -/
theorem exists_unit_lift_ramifiedResidue
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (a : (ZMod p)ˣ) :
    ∃ e : (𝓞 K)ˣ, ramifiedReduction hζ hodd (e : 𝓞 K) = (a : ZMod p) := by
  let S := ∑ k ∈ Finset.range a.val.val, hζ.toInteger ^ k
  have hS : IsUnit S := hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit hp.out.two_le
    (ZMod.val_coe_unit_coprime a)
  refine ⟨hS.unit, ?_⟩
  rw [hS.unit_spec]
  simp only [S, ramifiedReduction_geom_sum, ZMod.natCast_zmod_val]

end DkMath.Lib.NumberTheory
