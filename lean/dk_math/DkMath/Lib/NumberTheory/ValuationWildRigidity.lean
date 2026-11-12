/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean.
Modified: unit-period API, existing DkMath prime-support bridge, no P2M imports.
-/

import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import Mathlib.Algebra.Field.GeomSum

#print "file: DkMath.Lib.NumberTheory.ValuationWildRigidity"

/-!
# 野生合同と単元周期の剛性

野生合同から厳密な付値不等式を得て、作用差の軌道和を telescoping する。
単元周期の主項と、それより小さい誤差和は相殺しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationWildRigidity
open ValuationInertia ValuationPrimeSupport
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- 非零の分母に対する厳密な付値不等式を、比の非単元性へ翻訳する。 -/
theorem valuation_lt_iff_div_mem_nonunits (x y : L) (hy : y ≠ 0) :
    A.valuation x < A.valuation y ↔ x / y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀]
  exact (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hy))

/-- 全非零元の作用差が元より小さい、という野生合同の付値表示。 -/
def IsWildAt (σ : L ≃ₐ[K] L) : Prop := ∀ z : L, z ≠ 0 → A.valuation (σ z - z) < A.valuation z

/-- 模範解答と既存の Frobenius 誤差が持つ比の合同から、同じ付値条件を得る。 -/
theorem isWildAt_of_forall_mem_nonunits {σ : L ≃ₐ[K] L} (h : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) :
    IsWildAt A σ := by
  intro z hz
  rw [valuation_lt_iff_div_mem_nonunits A _ _ hz, sub_div, div_self hz, div_eq_mul_inv]
  exact h z hz

/-- 野生自己同型は付値を保つ。誤差が元より厳密に小さいことを使う。 -/
theorem IsWildAt.valuation_apply {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (w : L) : A.valuation (σ w) = A.valuation w := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have h := Valuation.map_add_eq_of_lt_right A.valuation (hw w hw0)
  rwa [sub_add_cancel] at h

/-- 野生合同は合成で保たれる。 -/
theorem IsWildAt.mul {σ τ : L ≃ₐ[K] L} (hσ : IsWildAt A σ) (hτ : IsWildAt A τ) :
    IsWildAt A (σ * τ) := by
  intro z hz
  have he : (σ * τ) z - z = σ (τ z - z) + (σ z - z) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [he]
  apply Valuation.map_add_lt _ _ (hσ z hz)
  rw [hσ.valuation_apply A]
  exact hτ z hz

/-- 野生合同は逆元で保たれる。 -/
theorem IsWildAt.inv {σ : L ≃ₐ[K] L} (hσ : IsWildAt A σ) : IsWildAt A σ⁻¹ := by
  intro z hz
  have hz' : σ⁻¹ z ≠ 0 := (map_ne_zero σ⁻¹).mpr hz
  have h := hσ (σ⁻¹ z) hz'
  have hv := hσ.valuation_apply A (σ⁻¹ z)
  have hcan : σ (σ⁻¹ z) = z := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [hcan] at h hv
  have he : σ⁻¹ z - z = -(z - σ⁻¹ z) := by ring
  rw [he, Valuation.map_neg]
  exact h.trans_eq hv.symm

/-- 剛性の付値条件と、全非零元の作用比による野生合同は同値。 -/
theorem isWildAt_iff {σ : L ≃ₐ[K] L} : IsWildAt A σ ↔
    ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits := by
  constructor
  · intro h z hz
    have h' := (valuation_lt_iff_div_mem_nonunits A _ _ hz).mp (h z hz)
    have he : (σ z - z) / z = σ z * z⁻¹ - 1 := by field_simp
    rw [← he]
    exact h'
  · exact isWildAt_of_forall_mem_nonunits A

/-- 全非零元の野生合同で定義する実際の自己同型部分群。 -/
def wildSubgroup : Subgroup (L ≃ₐ[K] L) where
  carrier := IsWildAt A
  one_mem' := by intro z hz; simpa using (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hz))
  mul_mem' hσ hτ := IsWildAt.mul A hσ hτ
  inv_mem' hσ := IsWildAt.inv A hσ

/-- 任意の自然数冪も、同じ全非零元の野生条件を満たす。 -/
theorem IsWildAt.pow {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (n : ℕ) : IsWildAt A (σ ^ n) := by
  induction n with
  | zero => intro z hz; simp [(map_ne_zero A.valuation).mpr hz, zero_lt_iff]
  | succ n ih =>
    intro z hz
    have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (hw z hz)
    rw [IsWildAt.valuation_apply A hw]
    exact ih z hz

/-- 周期 m が付値環の単元なら、その周期を持つ同じ元は既に固定される。 -/
theorem IsWildAt.fixed_of_unit_period {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) {m : ℕ} (hm : A.valuation (m : L) = 1) (y : L) (hy : (σ ^ m) y = y) : σ y = y := by
  by_contra hne
  set w := σ y - y with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  -- 周期の望遠和は零。
  have htel : (Finset.range m).sum (fun i => (σ ^ i) w) = 0 := by
    have h := Finset.sum_range_sub (fun i => (σ ^ i) y) m
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [hy, sub_self] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
  -- 各項を主項 w と小さい誤差に分ける。
  have hdec : (Finset.range m).sum (fun i => (σ ^ i) w)
      = (m : L) * w + (Finset.range m).sum (fun i => (σ ^ i) w - w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w - w)) < A.valuation ((m : L) * w) := by
    rw [map_mul, hm, one_mul]
    exact Valuation.map_sum_lt _ ((map_ne_zero _).mpr hw0) (fun i _ => (IsWildAt.pow A hw i) w hw0)
  have hval : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w)) = A.valuation ((m : L) * w) := by
    rw [hdec, add_comm]
    exact Valuation.map_add_eq_of_lt_right _ hS
  rw [htel, map_zero, map_mul, hm, one_mul, eq_comm, map_eq_zero] at hval
  exact hw0 hval

/-- q 上の野生合同を満たす自己同型は、q と互いに素な周期を持つ同じ元を固定する。 -/
theorem fixed_of_coprime_period {q m : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    {σ : L ≃ₐ[K] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) {y : L} (hy : (σ ^ m) y = y) : σ y = y := by
  have hnot : ¬ (q : ℤ) ∣ (m : ℤ) := by
    exact_mod_cast ((Nat.Prime.coprime_iff_not_dvd hq).mp hm.symm)
  have hu : A.valuation (m : L) = 1 := by
    simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) hnot
  exact IsWildAt.fixed_of_unit_period A (isWildAt_of_forall_mem_nonunits A hwild) hu y hy

end DkMath.Lib.NumberTheory.ValuationWildRigidity
