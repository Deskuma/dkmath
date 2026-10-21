/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.lean.
Upstream blob: 98fe0128d5c2a913dd127b273fb542d7d5102761
Modified for DkMath: isolate actual Dedekind valuation transport from elliptic geometry.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

#print "file: DkMath.Lib.Algebra.DedekindValuationEquiv"

/-!
# 環同型で付値の正規化を保つ

付値環の同値にとどまらず、素イデアルの冪への所属を比較して整数指数を固定する。
分数体への写像が座標環の同型と可換なら、非零分母を持つ表示で任意の有理関数へ延長できる。
-/
open scoped nonZeroDivisors
namespace IsDedekindDomain.HeightOneSpectrum
variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
/-- 環同型は素イデアルの冪への所属を正確に保存する。 -/
theorem mem_comap_pow_iff (e : R ≃+* S) (v : HeightOneSpectrum S) (r : R) (n : ℕ) :
    r ∈ (v.comap (e : R →+* S) e.surjective).asIdeal ^ n ↔ e r ∈ v.asIdeal ^ n := by
  change r ∈ (v.asIdeal.comap e) ^ n ↔ e r ∈ v.asIdeal ^ n
  rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

/-- 冪への所属の判定から、正規化された整数付値そのものの一致を得る。 -/
theorem intValuation_comap_ringEquiv (e : R ≃+* S) (v : HeightOneSpectrum S) (r : R) :
    (v.comap (e : R →+* S) e.surjective).intValuation r = v.intValuation (e r) := by
  by_cases hr : r = 0
  · simp [hr]
  have her : e r ≠ 0 := (map_ne_zero_iff e e.injective).mpr hr
  set w := v.comap (e : R →+* S) e.surjective
  classical
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, w.intValuation r = WithZero.exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_if_neg hr⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℕ, v.intValuation (e r) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, v.intValuation_if_neg her⟩
  apply le_antisymm
  · rw [hm₂, intValuation_le_pow_iff_mem, mem_comap_pow_iff, ← intValuation_le_pow_iff_mem, ← hm₂]
  · rw [hm₁, intValuation_le_pow_iff_mem, ← mem_comap_pow_iff, ← intValuation_le_pow_iff_mem, ← hm₁]

/-- 座標環上の一致を、実際の分子・分母の表示で分数体全体へ延長する。 -/
theorem valuation_comap_ringEquiv (e : R ≃+* S) (ψ : K →+* L)
    (hψ : ∀ r : R, ψ (algebraMap R K r) = algebraMap S L (e r)) (v : HeightOneSpectrum S) (x : K) :
    v.valuation L (ψ x) = (v.comap (e : R →+* S) e.surjective).valuation K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, hψ, hψ, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_comap_ringEquiv,
    intValuation_comap_ringEquiv]

end IsDedekindDomain.HeightOneSpectrum
