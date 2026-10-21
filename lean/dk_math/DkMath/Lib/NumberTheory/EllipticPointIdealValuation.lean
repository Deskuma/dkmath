/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilNum.lean.
Upstream blob: 74864cced2b6198ce5ee7d72f60cb748f7647cab
Modified for DkMath: arbitrary point-ideal generators; reuse proved point ideals and places.
-/

import DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
import Mathlib.RingTheory.DedekindDomain.AdicValuation

#print "file: DkMath.Lib.NumberTheory.EllipticPointIdealValuation"

/-!
# 相異なる有限点の積を生成する元の付値

座標環がDedekind整域なら、有限点Pの素イデアルは離散付値を定める。
点集合の積を生成するrについて、Pが集合に入ればrはその素イデアルには入るが二乗には入らない。
集合に入らなければrはその素イデアルに入らない。従って重複度はそれぞれ1と0になる。
乗法的付値の規約はv(r)=exp(−ord(r))であり、零点に対応する値はexp(−1)<1である。
Oの寄与は単位イデアルとし、O自身を測定する付値は導入しない。
-/
open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
namespace DkMath.Lib.NumberTheory.EllipticPointIdealValuation
open EllipticFunctionField EllipticPrincipalPointIdeal
variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [IsDedekindDomain (W⁄K).CoordinateRing]

omit [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 非零点の点イデアルは、既存の同じ有限場所の素イデアルに一致する。 -/
theorem pointIdeal_eq_placeOf {P : (W⁄K).Point} (hP : P ≠ 0) :
    pointIdeal P = (placeOf W K P hP).asIdeal := pointIdeal_of_ne_zero hP

open Classical in
/-- 同じ点集合の積を生成する任意のrの付値公式。
重複を持たないFinsetであることと、場所から点を復元できることが二重零点を排除する。 -/
theorem intValuation_of_span_eq_prod (s : Finset (W⁄K).Point) {r : (W⁄K).CoordinateRing}
    (hr : Ideal.span {r} = ∏ P ∈ s, pointIdeal P) (P₁ : (W⁄K).Point) (hP₁ : P₁ ≠ 0) :
    (placeOf W K P₁ hP₁).intValuation r = if P₁ ∈ s then exp (-1) else 1 := by
  classical
  set v := placeOf W K P₁ hP₁ with hv
  have hr0 : r ≠ 0 := by
    intro h
    apply prod_pointIdeal_ne_bot s id
    change (∏ P ∈ s, pointIdeal P) = ⊥
    rw [← hr, h, Ideal.span_singleton_eq_bot.mpr rfl]
  -- 素イデアルの包含から、同じ有限点であることを復元する。
  have hle : ∀ P ∈ s, pointIdeal P ≤ v.asIdeal → P = P₁ := by
    intro P _ hPle
    by_cases hP0 : P = 0
    · exfalso
      rw [hP0, pointIdeal_zero, top_le_iff] at hPle
      exact v.isPrime.ne_top hPle
    · rw [pointIdeal_eq_placeOf W K hP0] at hPle
      have heq : (placeOf W K P hP0).asIdeal = v.asIdeal :=
        (placeOf W K P hP0).isMaximal.eq_of_le v.isPrime.ne_top hPle
      exact placeOf_injective W K hP0 hP₁ (HeightOneSpectrum.ext heq)
  -- 集合の中にある点は一度だけ現れる。二乗で割れないことが重複度1を保証する。
  by_cases hmem : P₁ ∈ s
  · rw [ite_eq_left hmem]
    have hsplit := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem (fun P => pointIdeal P)
    have hmem1 : r ∈ v.asIdeal ^ 1 := by
      rw [pow_one, ← Ideal.span_singleton_le_iff_mem, hr, hsplit, hv, ← pointIdeal_eq_placeOf W K hP₁]
      exact Ideal.mul_le_left
    have hnot2 : r ∉ v.asIdeal ^ 2 := by
      intro h2
      rw [← Ideal.dvd_span_singleton, hr, hsplit, pointIdeal_eq_placeOf W K hP₁, ← hv, sq] at h2
      have h3 : v.asIdeal ∣ ∏ P ∈ s \ {P₁}, pointIdeal P :=
        (mul_dvd_mul_iff_left v.ne_bot).mp h2
      rw [Ideal.dvd_iff_le] at h3
      obtain ⟨P, hPs, hPle⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp h3
      have hPP := hle P (Finset.mem_sdiff.mp hPs).1 hPle
      exact (Finset.mem_sdiff.mp hPs).2 (Finset.mem_singleton.mpr hPP)
    have hle1 : v.intValuation r ≤ exp (-((1 : ℕ) : ℤ)) := (intValuation_le_pow_iff_mem v r 1).mpr hmem1
    have hgt2 : ¬ v.intValuation r ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
      hnot2 ((intValuation_le_pow_iff_mem v r 2).mp h)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, v.intValuation r = exp z :=
      ⟨_, (exp_log (intValuation_ne_zero v r hr0)).symm⟩
    rw [hz] at hle1 hgt2 ⊢
    rw [exp_le_exp] at hle1 hgt2
    push_cast at hle1 hgt2
    congr 1
    omega
  · rw [ite_eq_right hmem, intValuation_eq_one_iff]
    intro hrv
    rw [← Ideal.span_singleton_le_iff_mem, hr] at hrv
    obtain ⟨P, hPs, hPle⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp hrv
    exact hmem (hle P hPs hPle ▸ hPs)

/-- 生成元の選択が異なっても、同じ積を生成すれば全ての有限点で付値は一致する。 -/
theorem intValuation_generator_independent (s : Finset (W⁄K).Point) {r t : (W⁄K).CoordinateRing}
    (hr : Ideal.span {r} = ∏ P ∈ s, pointIdeal P)
    (ht : Ideal.span {t} = ∏ P ∈ s, pointIdeal P) (P : (W⁄K).Point) (hP : P ≠ 0) :
    (placeOf W K P hP).intValuation r = (placeOf W K P hP).intValuation t := by
  classical
  rw [intValuation_of_span_eq_prod W K s hr P hP, intValuation_of_span_eq_prod W K s ht P hP]

end DkMath.Lib.NumberTheory.EllipticPointIdealValuation
