/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.lean.
Upstream blob: 7b00f567f061b8924a0d23d55b057de611121a78
Modified for DkMath: reusable normalized valuation descent, with all surjectivity and pullback guards explicit.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation

#print "file: DkMath.Lib.Algebra.PullbackPrincipalPrime"

/-!
# 単純零点を引き戻しの像から主素イデアルへ戻す

正規化された付値の不等式だけを使い、付値の完全一致や非分岐性を仮定しない。
素点の原像の存在と、特別な関数の一重零点が必要な強さを供給する。
-/
namespace DkMath.Lib.Algebra.PullbackPrincipalPrime
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- 離散な整数値付値では、1未満なら正規化された最初の零点値以下になる。 -/
theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← exp_log h0] at hx ⊢
    rw [← exp_zero, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

omit [IsDedekindDomain R] in
/-- 全非零素イデアルを避ける元は単元である。零でない素点を一つ明示して退化を避ける。 -/
theorem isUnit_of_forall_not_mem [IsDomain R] {r : R} (hr : ∀ w : HeightOneSpectrum R, r ∉ w.asIdeal)
    (w₀ : HeightOneSpectrum R) : IsUnit r := by
  by_contra hu
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {r}) (Ideal.span_singleton_ne_top hu)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr w₀ (Submodule.zero_mem _)
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => by
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hr0 hle
  exact hr ⟨𝔪, h𝔪.isPrime, h𝔪0⟩ (hle (Ideal.mem_span_singleton_self r))

/-- 付値の上界を保つ引き戻しμと素点写像Nについて、各素点が像を持つとする。
μ(h)がt₀の原像だけで一重零点、他の有限像では付値1なら、t₀は主イデアルである。
まずhの極を逆数の付値で排除し、整元rへ戻す。rの零点はt₀だけで二重零点ではないので、
(t₀)を割り出した残余イデアルは単位イデアルとなる。N=Noneの点は除外したまま保持する。 -/
theorem exists_eq_span_of_eq_pullback (μ : K →+* K)
    (N : HeightOneSpectrum R → Option (HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w)
    (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ),
      w.valuation K h ≤ exp (-(k : ℤ)) → v.valuation K (μ h) ≤ exp (-(k : ℤ)))
    (g : K) (t₀ : HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = exp (-1))
    (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) :
    ∃ r : R, t₀.asIdeal = Ideal.span {r} := by
  obtain ⟨h, rfl⟩ := hgμ
  obtain ⟨v₀, hv₀⟩ := hN t₀
  have hg_le : ∀ v w, N v = some w → v.valuation K (μ h) ≤ 1 := by
    intro v w hvw
    by_cases hw : w = t₀
    · subst hw; rw [hg₀ v hvw, ← exp_zero, exp_le_exp]; norm_num
    · rw [hg₁ v w hvw hw]
  have hμ0 : ∀ v w, N v = some w → ∀ x : K, w.valuation K x ≤ 1 → v.valuation K (μ x) ≤ 1 := by
    intro v w hvw x hx
    have := hμ v w hvw x 0 (by rwa [Nat.cast_zero, neg_zero, exp_zero])
    rwa [Nat.cast_zero, neg_zero, exp_zero] at this
  have hh0 : h ≠ 0 := by
    rintro rfl
    have := hg₀ v₀ hv₀
    rw [map_zero, Valuation.map_zero] at this
    exact WithZero.zero_ne_coe this
  have hμh0 : μ h ≠ 0 := (map_ne_zero μ).mpr hh0
  have h1 : ∀ w : HeightOneSpectrum R, w.valuation K h ≤ 1 := by
    intro w
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hv⟩ := hN w
    have hinv : w.valuation K h⁻¹ ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one, map_inv₀]
      exact le_exp_neg_one_of_lt_one ((inv_lt_one₀ (lt_trans zero_lt_one hlt)).mpr hlt)
    have := hμ v w hv h⁻¹ 1 hinv
    rw [map_inv₀, map_inv₀, Nat.cast_one] at this
    have hlt' : (v.valuation K (μ h))⁻¹ < 1 := lt_of_le_of_lt this (by
      rw [← exp_zero, exp_lt_exp]; norm_num)
    have hpos : 0 < v.valuation K (μ h) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hμh0)
    exact absurd ((inv_lt_one₀ hpos).mp hlt') (not_lt.mpr (hg_le v w hv))
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one K h h1
  subst hr
  have hr0 : r ≠ 0 := fun h0 => hh0 (by rw [h0, map_zero])
  have h3 : ∀ w : HeightOneSpectrum R, w ≠ t₀ → r ∉ w.asIdeal := by
    intro w hw hmem
    obtain ⟨v, hv⟩ := hN w
    have hlt : w.valuation K (algebraMap R K r) ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one]
      exact le_exp_neg_one_of_lt_one ((valuation_lt_one_iff_mem w r).mpr hmem)
    have := hμ v w hv _ 1 hlt
    rw [hg₁ v w hv hw, Nat.cast_one, ← exp_zero, exp_le_exp] at this
    norm_num at this
  have h4a : r ∈ t₀.asIdeal := by
    by_contra hnot
    have hunit : IsUnit r := isUnit_of_forall_not_mem
      (fun w => by by_cases hw : w = t₀ <;> [exact hw ▸ hnot; exact h3 w hw]) t₀
    obtain ⟨u, hu⟩ := hunit
    have hprod : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one, map_one]
    have hle : v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ 1 :=
      hμ0 v₀ t₀ hv₀ _ (valuation_le_one t₀ _)
    have key : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ exp (-1) * 1 := by
      rw [hg₀ v₀ hv₀]
      gcongr
    rw [hprod, mul_one, ← exp_zero, exp_le_exp] at key
    norm_num at key
  have h4b : r ∉ t₀.asIdeal ^ 2 := by
    intro hmem
    have hle : t₀.valuation K (algebraMap R K r) ≤ exp (-((2 : ℕ) : ℤ)) := by
      rw [valuation_of_algebraMap]
      exact (intValuation_le_pow_iff_mem t₀ r 2).mpr hmem
    have := hμ v₀ t₀ hv₀ _ 2 hle
    rw [hg₀ v₀ hv₀, exp_le_exp] at this
    norm_num at this
  refine ⟨r, ?_⟩
  have hdvd : t₀.asIdeal ∣ Ideal.span {r} :=
    (Ideal.dvd_span_singleton).mpr h4a
  obtain ⟨J, hJ⟩ := hdvd
  suffices hJtop : J = ⊤ by rw [hJ, hJtop, Ideal.mul_top]
  by_contra hJtop
  obtain ⟨𝔪, h𝔪, hJle⟩ := Ideal.exists_le_maximal J hJtop
  have hJ0 : J ≠ ⊥ := by
    intro hJ0
    rw [hJ0, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hr0 hJ
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hJle))
  set w : HeightOneSpectrum R := ⟨𝔪, h𝔪.isPrime, h𝔪0⟩
  have hrw : r ∈ t₀.asIdeal * w.asIdeal := by
    have : t₀.asIdeal * w.asIdeal ∣ Ideal.span {r} := by
      rw [hJ]; exact mul_dvd_mul_left _ ((Ideal.dvd_iff_le).mpr hJle)
    exact (Ideal.dvd_span_singleton).mp this
  by_cases hw : w = t₀
  · apply h4b
    rw [sq, ← hw]
    nth_rewrite 1 [hw]
    exact hrw
  · exact h3 w hw (Ideal.mul_le_right hrw)


end DkMath.Lib.Algebra.PullbackPrincipalPrime
