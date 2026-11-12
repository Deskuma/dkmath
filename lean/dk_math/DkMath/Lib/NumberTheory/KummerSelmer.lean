/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKummerWeight
import DkMath.Lib.NumberTheory.DedekindFractionalValuation
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.ClassGroup.Basic

#print "file: DkMath.Lib.NumberTheory.KummerSelmer"

/-!
# 同じ Kummer 類の付値条件と主分数イデアルの冪

Mathlib の Selmer 群を、既存の Kummer 商と同じ商として読む。
全素点の付値を法 `p` で取る線形写像と、その共通核を構成する。
主分数イデアルの指数との符号を明示し、所属を指数の可除性で判定する。
この所属は局所不分岐の同義語として仮定せず、別の算術的証明義務に保つ。
-/

namespace DkMath.Lib.NumberTheory.KummerSelmer

open CyclotomicKummerWeight IsDedekindDomain WithZero
open scoped nonZeroDivisors
noncomputable section

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

/-- 同じ商上の Mathlib の実際の付値を加法的な線形写像に読む。 -/
def valuationLinear (p : ℕ) (v : HeightOneSpectrum R) :
    Additive (KummerClass F p) →ₗ[ZMod p] ZMod p :=
  (v.valuationOfNeZeroMod p).toAdditiveLeft.toZModLinearMap p

/-- 全ての有限素点で付値が `p` の倍数になる部分加群。 -/
def valuationSpace (p : ℕ) : Submodule (ZMod p) (Additive (KummerClass F p)) :=
  ⨅ v : HeightOneSpectrum R, (valuationLinear (F := F) p v).ker

theorem mem_valuationSpace_iff (p : ℕ) (x : Additive (KummerClass F p)) :
    x ∈ valuationSpace (R := R) p ↔ ∀ v : HeightOneSpectrum R, valuationLinear p v x = 0 := by
  simp only [valuationSpace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- この部分加群は Mathlib の `S=∅` Selmer 群を同じ商上で読んだものである。 -/
theorem mem_valuationSpace_iff_selmer (p : ℕ) (x : KummerClass F p) :
    Additive.ofMul x ∈ valuationSpace (R := R) p ↔
      x ∈ (IsDedekindDomain.selmerGroup (R := R) (K := F)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := p)) := by
  rw [mem_valuationSpace_iff]
  change (∀ v : HeightOneSpectrum R, (v.valuationOfNeZeroMod p x).toAdd = 0) ↔
    ∀ v : HeightOneSpectrum R, v ∉ (∅ : Set (HeightOneSpectrum R)) → v.valuationOfNeZeroMod p x = 1
  constructor
  · intro h v _
    exact Multiplicative.toAdd.injective (h v)
  · intro h v
    exact congrArg Multiplicative.toAdd (h v (Set.notMem_empty v))

/-- 正のイデアル指数は Mathlib の乗法的付値の加法表示の負号である。 -/
theorem count_span_eq_neg_valuation (v : HeightOneSpectrum R) (x : Fˣ) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (x : F)) =
      -(v.valuationOfNeZero x).toAdd := by
  have h := DedekindFractionalValuation.count_spanSingleton v (x : F) x.ne_zero
  rw [← v.valuationOfNeZero_eq x] at h
  exact h

/-- 商上の付値の値を、同じ代表元の整数付値で計算する。 -/
theorem valuationLinear_mk (p : ℕ) (v : HeightOneSpectrum R) (x : Fˣ) :
    valuationLinear p v (Additive.ofMul (x : KummerClass F p)) =
      ((v.valuationOfNeZero x).toAdd : ZMod p) := by
  rfl

/-- 付値の線形写像の零条件は、同じ主分数イデアルの指数の可除性。 -/
theorem valuationLinear_eq_zero_iff (p : ℕ) (v : HeightOneSpectrum R) (x : Fˣ) :
    valuationLinear p v (Additive.ofMul (x : KummerClass F p)) = 0 ↔
      (p : ℤ) ∣ FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (x : F)) := by
  rw [valuationLinear_mk, count_span_eq_neg_valuation, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg]

/-- 代表元の選択をし直さず、同じ Kummer 類の Selmer 所属を指数で判定する。 -/
theorem mem_valuationSpace_mk_iff (p : ℕ) (x : Fˣ) :
    Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p ↔
      ∀ v : HeightOneSpectrum R,
        (p : ℤ) ∣ FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (x : F)) := by
  rw [mem_valuationSpace_iff]
  exact forall_congr' fun v => valuationLinear_eq_zero_iff p v x

/-- 整数環の単元由来の Kummer 類は全素点の付値条件を満たす。 -/
theorem unit_mem_valuationSpace (p : ℕ) (u : Rˣ) :
    Additive.ofMul ((Units.map (algebraMap R F).toMonoidHom u : Fˣ) : KummerClass F p) ∈
      valuationSpace (R := R) p := by
  rw [mem_valuationSpace_iff_selmer]
  exact (IsDedekindDomain.selmerGroup.fromUnit (K := F) (n := p) u).property

/-- `p` 乗根を持つ非零分数イデアルは、全指数が `p` の倍数になる。 -/
theorem count_dvd_of_eq_pow (p : ℕ) {I J : FractionalIdeal R⁰ F} (h : I = J ^ p)
    (v : HeightOneSpectrum R) : (p : ℤ) ∣ FractionalIdeal.count F v I := by
  rw [h, FractionalIdeal.count_pow]
  exact dvd_mul_right _ _

/-- 代表元を `c^p` 倍すると、同じ主分数イデアルの指数には `p` 倍だけ加わる。 -/
theorem count_span_mul_pow (p : ℕ) (v : HeightOneSpectrum R) (c x : Fˣ) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ ((c : F) ^ p * (x : F))) =
      p * FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (c : F)) +
        FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (x : F)) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_mul]
  · rw [FractionalIdeal.count_pow]
  · exact pow_ne_zero p (FractionalIdeal.spanSingleton_ne_zero_iff.mpr c.ne_zero)
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero

/-- 全素点の指数が `p` の倍数なら、実際の同じ分数イデアルの `p` 乗根を構成できる。 -/
theorem exists_fractionalIdeal_pow (p : ℕ) {I : FractionalIdeal R⁰ F} (hI : I ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum R, (p : ℤ) ∣ FractionalIdeal.count F v I) :
    ∃ J : FractionalIdeal R⁰ F, J ≠ 0 ∧ J ^ p = I := by
  let e : HeightOneSpectrum R → ℤ := fun v => FractionalIdeal.count F v I / p
  have he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0 := by
    filter_upwards [FractionalIdeal.finite_factors I] with v hv
    change FractionalIdeal.count F v I / p = 0
    rw [hv, Int.zero_ediv]
  let J : FractionalIdeal R⁰ F := ∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal R⁰ F) ^ e v
  have hJ : J ≠ 0 := finprod_ne_zero fun v =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  refine ⟨J, hJ, DedekindFractionalValuation.ext_count (pow_ne_zero p hJ) hI ?_⟩
  intro v
  rw [FractionalIdeal.count_pow, FractionalIdeal.count_finprod F v e he]
  exact Int.mul_ediv_cancel' (hdiv v)

/-- Selmer 所属から、同じ代表元の主分数イデアルの実際の冪分解へ。 -/
theorem exists_principal_fractionalIdeal_pow (p : ℕ) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    ∃ J : FractionalIdeal R⁰ F, J ≠ 0 ∧
      J ^ p = FractionalIdeal.spanSingleton R⁰ (x : F) :=
  exists_fractionalIdeal_pow p (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
    ((mem_valuationSpace_mk_iff p x).mp hx)

/-- 正の指数では非零分数イデアルの冪根は一意。元の生成元は取り替えない。 -/
theorem fractionalIdeal_pow_injective {p : ℕ} (hp : 0 < p)
    {I J : FractionalIdeal R⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0) (he : I ^ p = J ^ p) : I = J := by
  apply DedekindFractionalValuation.ext_count hI hJ
  intro v
  have h := congrArg (FractionalIdeal.count F v) he
  rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at h
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp.ne') h

/-- Selmer 所属が証明された場合、同じ主分数イデアルの冪根から実際の類群の `p` 捩れが得られる。
所属や類群成分の消滅を内部供給したという主張ではない。 -/
theorem exists_classGroup_torsion (p : ℕ) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    ∃ (J : FractionalIdeal R⁰ F) (hJ : J ≠ 0),
      J ^ p = FractionalIdeal.spanSingleton R⁰ (x : F) ∧
      (ClassGroup.mk F (Units.mk0 J hJ)) ^ p = 1 := by
  obtain ⟨J, hJ, he⟩ := exists_principal_fractionalIdeal_pow p x hx
  refine ⟨J, hJ, he, ?_⟩
  rw [← map_pow]
  apply ClassGroup.mk_eq_one_iff.mpr
  change (↑(J ^ p : FractionalIdeal R⁰ F) : Submodule R F).IsPrincipal
  rw [he, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(x : F), rfl⟩⟩

end
end DkMath.Lib.NumberTheory.KummerSelmer
