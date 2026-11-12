/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_frey_exists_inertia_not_fixed_at_two.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: arbitrary fields, arbitrary unit exponent, separate public power rigidity API.
-/

import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import Mathlib.Algebra.Ring.GeomSum

#print "file: DkMath.Lib.NumberTheory.ValuationInertiaPower"

/-!
# NOTE-032-002A: 単元の冪と慣性作用の剛性

[DkMath.Lib] 素数2やFrey曲線に依存しない冪の補題を公開する。
指数nが付値環の単元なら、非自明なn乗根ζと1の差も単元となる。
一方、慣性元は整元を剰余体で固定する。この二つを合わせると、
単元wのn乗を固定する慣性元はw自身も固定する。

wが単元という仮定は本質的である。非単元のn乗根を慣性が動かす現象は、
次のKummerInertiaで扱う。野生慣性の消滅とは区別する。
-/
namespace DkMath.Lib.NumberTheory.ValuationInertiaPower
open ValuationInertia ValuationPrimeSupport
variable {K : Type*} [Field K]

/-- [DkMath.Lib] 非自明なp乗根に対する二重幾何級数の因数分解。
pの素数性を仮定せず、p=(1−ζ)ΣᵢΣⱼζʲを環の恒等式から導く。 -/
theorem natCast_eq_one_sub_mul_sum {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} {ζ : R}
    (hζ : ζ ^ p = 1) (hne : ζ ≠ 1) :
    (p : R) = (1 - ζ) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
  have hsum0 : ∑ i ∈ Finset.range p, ζ ^ i = 0 := by
    have h1 : (∑ i ∈ Finset.range p, ζ ^ i) * (ζ - 1) = 0 := by
      rw [geom_sum_mul, hζ, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  calc (p : R) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
        rw [Finset.sum_sub_distrib, hsum0, sub_zero, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
    _ = ∑ i ∈ Finset.range p, (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hgs := geom_sum_mul ζ i
        linear_combination hgs
    _ = (1 - ζ) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
        rw [Finset.mul_sum]

/-- [DkMath.Lib] 単元指数の非自明な冪根は、1との差も単元である。
二重幾何級数の積の付値が1で、両因子が整であることを使う。 -/
theorem valuation_sub_one_eq_one {A : ValuationSubring K} {p : ℕ}
    (hp : p ≠ 0) (hvp : A.valuation (p : K) = 1) {ζ : K} (hζ : ζ ^ p = 1) (hne : ζ ≠ 1) :
    A.valuation (ζ - 1) = 1 := by
  have hvζ : A.valuation ζ = 1 := by
    refine pow_left_injective (M := A.ValueGroup) hp ?_
    change A.valuation ζ ^ p = 1 ^ p
    rw [← map_pow, hζ, map_one, one_pow]
  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hvζ.le
  have hYA : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
    sum_mem fun i _ => sum_mem fun j _ => pow_mem hζA j
  have h1A : (1 - ζ) ∈ A := sub_mem (one_mem A) hζA
  have hfact := natCast_eq_one_sub_mul_sum hζ hne
  have hvmul : A.valuation (1 - ζ) *
      A.valuation (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) = 1 := by
    rw [← map_mul, ← hfact]
    exact hvp
  have hle1 : A.valuation (1 - ζ) ≤ 1 := (A.valuation_le_one_iff _).mpr h1A
  have hleY : A.valuation (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr hYA
  have h1 : A.valuation (1 - ζ) = 1 := by
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · exact absurd hvmul (mul_lt_one_of_lt_of_le hlt hleY).ne
    · exact heq
  calc A.valuation (ζ - 1) = A.valuation (-(1 - ζ)) := by rw [neg_sub]
    _ = A.valuation (1 - ζ) := Valuation.map_neg _ _
    _ = 1 := h1

/-- [DkMath.Lib] 指数nが単元なら、単元のn乗を固定する慣性元は元も固定する。
τw/wはn乗根であり、非自明ならτw−wは単元になるが、慣性の剰余合同に反する。 -/
theorem inertia_fixed_of_unit_pow (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]
    {n : ℕ} (hn : n ≠ 0) (hnv : A.valuation (n : K) = 1)
    (σ : K ≃ₐ[F] K) (hσ : σ ∈ inertiaSubgroupIn A F)
    {w : K} (hw : A.valuation w = 1) (hpow : σ (w ^ n) = w ^ n) : σ w = w := by
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hζ : (σ w / w) ^ n = 1 := by
    rw [div_pow, ← map_pow, hpow, div_self (pow_ne_zero n hw0)]
  have hsmall := (ValuationSubring.mem_nonunits_iff A).mp
    (inertia_apply_sub_mem_nonunits A F σ hσ ((A.valuation_le_one_iff w).mp hw.le))
  by_contra hne
  have hne1 : σ w / w ≠ 1 := fun h => hne ((div_eq_one_iff_eq hw0).mp h)
  have hv := valuation_sub_one_eq_one hn hnv hζ hne1
  have hfac : σ w - w = (σ w / w - 1) * w := by field_simp
  rw [hfac, map_mul, hv, hw, mul_one] at hsmall
  exact lt_irrefl _ hsmall

/-- [DkMath.Lib] 指数nが単元なら、全n乗根は慣性に固定される。
剰余標数と指数が異なる場合の「根の枝は慣性で混ざらない」を表す。 -/
theorem inertia_fixed_of_pow_eq_one (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]
    {n : ℕ} (hn : n ≠ 0) (hnv : A.valuation (n : K) = 1)
    (σ : K ≃ₐ[F] K) (hσ : σ ∈ inertiaSubgroupIn A F)
    {ζ : K} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hvζ : A.valuation ζ = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hn
    change A.valuation ζ ^ n = 1 ^ n
    rw [← map_pow, hζ, map_one, one_pow]
  exact inertia_fixed_of_unit_pow A F hn hnv σ hσ hvζ (by rw [hζ, map_one])

end DkMath.Lib.NumberTheory.ValuationInertiaPower
