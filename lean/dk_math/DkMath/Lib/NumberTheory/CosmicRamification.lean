/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicCyclotomicNorm

/-!
# GN の因子と分岐イデアル

`λ = ζ-1` とおく。全ての円分因子は mod λ で gap x に一致する。
整数座標では `λ ∣ x` と `p ∣ x` が同値なので、非分岐側と分岐側の
分岐条件を正確に読み替えられる。

分岐側では全 p-1 個の非自明な因子から λ を一つずつ取り出せる。
従って `λ^(p-1) ∣ GN`。一方 `(λ)^(p-1)=(p)` である。
さらに整数座標の原始的な分岐側では、各非自明因子から λ をちょうど一つ
剥がせることを示す。剥離後の p 乗性と降下の構成は後続の課題である。
-/

open scoped BigOperators NumberField
open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

namespace DkMath.Lib.NumberTheory

/-- 全円分因子は mod `ζ-1` で gap に一致する。
原始根・素数次数を仮定しない可換環の可除性恒等式である。 -/
theorem sub_one_dvd_phaseFactor_iff_gap
    {R : Type*} [CommRing R] (ζ x u : R) (i : ℕ) :
    ζ - 1 ∣ x + (1 - ζ ^ i) * u ↔ ζ - 1 ∣ x := by
  have hd : ζ - 1 ∣ (1 - ζ ^ i) * u := by
    apply dvd_mul_of_dvd_left
    have h := sub_dvd_pow_sub_pow ζ (1 : R) i
    simpa only [one_pow, neg_sub] using dvd_neg.mpr h
  constructor
  · intro h
    have ht := dvd_sub h hd
    simpa using ht
  · intro h
    exact dvd_add h hd

/-- 分岐因子が gap を割る場合、GN の各非自明因子から一つずつ抽出できる。
素数でない次数でも、原始根による全因子分解があれば成立する下界である。 -/
theorem ramified_pow_dvd_GTail
    {R : Type*} [CommRing R] [IsDomain R]
    {d : ℕ} {ζ x u : R} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (hx : ζ - 1 ∣ x) : (ζ - 1) ^ (d - 1) ∣ GTail d 1 x u := by
  classical
  rw [GN_eq_nontrivial_phase_prod_range hd hζ]
  have h := Finset.prod_dvd_prod_of_dvd (s := (Finset.range d).erase 0)
    (fun _ => ζ - 1) (fun i => x + (1 - ζ ^ i) * u)
    (fun i _ => (sub_one_dvd_phaseFactor_iff_gap ζ x u i).mpr hx)
  simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hd),
    Finset.card_range] using h

/-- 円分整数環の分岐イデアルの基本等式 `(ζ-1)^(p-1)=(p)`。
元については単元の違いがあるため、主イデアルに移して等式にする。 -/
theorem ramifiedIdeal_pow_eq_prime_span
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) ^ (p - 1) =
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  exact IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ

/-- 整数座標で、全ての phase factor の分岐可除性は `p ∣ x` と同値。
これは整数と円分整数環を結ぶ、Case I / II の正確な境界である。 -/
theorem ramified_dvd_integral_phaseFactor_iff
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x u : ℤ) (i : ℕ) :
    hζ.toInteger - 1 ∣ (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) ↔
      (p : ℤ) ∣ x := by
  rw [sub_one_dvd_phaseFactor_iff_gap, (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ)]

/-- 分岐側の整数 GN は p で割り切れる。
全非自明因子の λ の積と、整数の分岐可除性の対応から得る。
可除回数がちょうど一回という主張ではない。 -/
theorem prime_dvd_integral_GTail_of_dvd_gap
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x u : ℤ} (hx : (p : ℤ) ∣ x) :
    (p : ℤ) ∣ GTail p 1 x u := by
  have hxR : hζ.toInteger - 1 ∣ (x : 𝓞 K) :=
    (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).mpr hx
  have hd := ramified_pow_dvd_GTail (u := (u : 𝓞 K)) hp.out.pos hζ.toInteger_isPrimitiveRoot hxR
  have hp2 := hp.out.two_le
  have hphase : hζ.toInteger - 1 ∣ GTail p 1 (x : 𝓞 K) (u : 𝓞 K) :=
    (dvd_pow_self _ (by omega : p - 1 ≠ 0)).trans hd
  apply (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).mp
  simpa [GTail] using hphase

/-- 非自明な phase factor は、gap が λ² を含み parameter が λ を含まなければ、
λ² では割り切れない。`1-ζ^i` が λ と同伴であることが決定的な入力である。 -/
theorem ramified_square_not_dvd_phaseFactor
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : (ζ - 1) ^ 2 ∣ x) (hu : ¬ ζ - 1 ∣ u)
    {i : ℕ} (hi0 : i ≠ 0) (hi : i < p) :
    ¬ (ζ - 1) ^ 2 ∣ x + (1 - ζ ^ i) * u := by
  have hcop : i.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr
      (fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega))).symm
  have ha : Associated (1 - ζ ^ i) (ζ - 1) := by
    simpa only [neg_sub] using
      (hζ.associated_sub_one_pow_sub_one_of_coprime hcop).symm.neg_left
  intro hsquare
  have hdiff : (ζ - 1) ^ 2 ∣ (1 - ζ ^ i) * u := by
    have h := dvd_sub hsquare hx
    simpa only [add_sub_cancel_left] using h
  have hmul : (ζ - 1) ^ 2 ∣ (ζ - 1) * u :=
    (ha.mul_right u).dvd_iff_dvd_right.mp hdiff
  obtain ⟨q, hq⟩ := hmul
  apply hu
  refine ⟨q, ?_⟩
  exact mul_left_cancel₀ (hζ.sub_one_ne_zero hp.one_lt)
    (by simpa only [pow_two, mul_assoc] using hq)

/-- 分岐側で、各非自明因子から **ちょうど一つ** の λ を剥がす。
整数 x が p で割れ、u が p で割れず、p≥3 なら
`x+(1-ζ^i)u=λβ` かつ `λ ∤ β` となる。
ここでは剥離後のイデアルが p 乗であることや降下はまだ主張しない。 -/
theorem exists_ramified_phase_quotient_of_dvd_gap
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp3 : 3 ≤ p)
    {x u : ℤ} (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u)
    {i : ℕ} (hi0 : i ≠ 0) (hi : i < p) :
    ∃ β : 𝓞 K,
      (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) = (hζ.toInteger - 1) * β ∧
      ¬ hζ.toInteger - 1 ∣ β := by
  have hd := (ramified_dvd_integral_phaseFactor_iff hζ x u i).mpr hx
  obtain ⟨β, hβ⟩ := hd
  refine ⟨β, hβ, ?_⟩
  have hxR : (p : 𝓞 K) ∣ (x : 𝓞 K) := by
    obtain ⟨q, hq⟩ := hx
    exact ⟨(q : 𝓞 K), by exact_mod_cast hq⟩
  have hx2 : (hζ.toInteger - 1) ^ 2 ∣ (x : 𝓞 K) :=
    (pow_dvd_pow (hζ.toInteger - 1) (by omega : 2 ≤ p - 1)).trans
      ((IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd.trans hxR)
  have huR : ¬ hζ.toInteger - 1 ∣ (u : 𝓞 K) := by
    rwa [IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ]
  intro hdiv
  apply ramified_square_not_dvd_phaseFactor hp.out hζ.toInteger_isPrimitiveRoot hx2 huR hi0 hi
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_⟩
  rw [hβ, hq, pow_two, mul_assoc]

end DkMath.Lib.NumberTheory
