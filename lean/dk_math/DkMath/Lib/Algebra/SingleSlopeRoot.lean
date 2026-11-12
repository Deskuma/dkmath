/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean,
blob aa678c2894fcf3bab25d6a4bd9e4a7878dd58eb5 (valuation argument).
Modified: isolate arbitrary valued-field single-slope root lemma without Frey dependencies.
-/

import DkMath.Lib.Algebra.ValuationPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits

#print "file: DkMath.Lib.Algebra.SingleSlopeRoot"

/-!
# NOTE-031-004C: 全根が極なら一つの傾きしか残らない

整な多項式の係数が、付値1または最高係数の付値以下という二種類に限られるとする。
全根が付値1より大きい場合、最大付値の根の積を分離する。
二種類の係数条件から、その根群の積と最高係数の積の付値は1となる。
残りに根があれば定数項の付値が1を超え、係数の整性に反する。
従って全根の付値は等しく、その共通傾きは次数と最高係数で決まる。
Newton多角形の一傾斜の内容を、任意の順序値群で根の積から直接証明する。
-/
namespace DkMath.Lib.Algebra.SingleSlopeRoot

set_option autoImplicit false

open Polynomial

section OrderHelpers

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private lemma slope_mul_lt_mul_of_lt_of_le {a b c d : Γ₀} (hab : a < b) (hcd : c ≤ d)
    (hd : d ≠ 0) : a * c < b * d :=
  lt_of_le_of_lt (mul_le_mul_right hcd a)
    (lt_of_le_of_ne (mul_le_mul_left hab.le d) fun h => hab.ne (mul_right_cancel₀ hd h))

private lemma slope_mul_lt_mul_of_le_of_lt {a b c d : Γ₀} (hab : a ≤ b) (hcd : c < d)
    (hb : b ≠ 0) : a * c < b * d :=
  lt_of_le_of_lt (mul_le_mul_left hab c)
    (lt_of_le_of_ne (mul_le_mul_right hcd.le b) fun h => hcd.ne (mul_left_cancel₀ hb h))

private lemma slope_one_lt_pow {M : Γ₀} (hM : 1 < M) {s : ℕ} (hs : s ≠ 0) : 1 < M ^ s := by
  induction s with
  | zero => exact absurd rfl hs
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hM
    · have hMn : 1 < M ^ n := ih (by omega)
      have hM0 : M ≠ 0 := (zero_lt_one.trans hM).ne'
      calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
        _ < M ^ n * M := slope_mul_lt_mul_of_lt_of_le hMn hM.le hM0
        _ = M ^ (n + 1) := (pow_succ M n).symm

private lemma slope_one_le_prod {s : Multiset Γ₀} (h : ∀ x ∈ s, 1 ≤ x) : 1 ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons]
    calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
      _ ≤ a * t.prod :=
        mul_le_mul' (h a (Multiset.mem_cons_self a t))
          (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

private lemma slope_one_lt_prod {s : Multiset Γ₀} (hne : s ≠ 0) (h : ∀ x ∈ s, 1 < x) :
    1 < s.prod := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, rfl⟩ : ∃ t, s = a ::ₘ t := ⟨s.erase a, (Multiset.cons_erase ha).symm⟩
  rw [Multiset.prod_cons]
  have h1a : 1 < a := h a (Multiset.mem_cons_self a t)
  have h1t : 1 ≤ t.prod := slope_one_le_prod fun x hx => (h x (Multiset.mem_cons_of_mem hx)).le
  have ht0 : t.prod ≠ 0 := (lt_of_lt_of_le zero_lt_one h1t).ne'
  calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
    _ < a * t.prod := slope_mul_lt_mul_of_lt_of_le h1a h1t ht0

end OrderHelpers


variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation K Γ₀)

private lemma valuation_coeff_multisetProd_X_sub_C_le {t : Multiset K} {B : Γ₀}
    (ht : ∀ r ∈ t, v r ≤ B) (i : ℕ) :
    v (((t.map fun a => X - C a).prod).coeff i) ≤ B ^ (Multiset.card t - i) := by
  induction t using Multiset.induction generalizing i with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, Nat.zero_sub,
      pow_zero, Polynomial.coeff_one]
    split_ifs
    · simp only [v.map_one, le_refl]
    · simp only [v.map_zero, zero_le]
  | cons a t ih =>
    have hta : ∀ r ∈ t, v r ≤ B := fun r hr => ht r (Multiset.mem_cons_of_mem hr)
    have haB : v a ≤ B := ht a (Multiset.mem_cons_self a t)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases i with _ | j
    · rw [Polynomial.mul_coeff_zero]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
      rw [map_mul, v.map_neg, Nat.sub_zero]
      calc v a * v (((t.map fun a => X - C a).prod).coeff 0)
          ≤ B * B ^ (Multiset.card t - 0) := mul_le_mul' haB (ih hta 0)
        _ = B ^ (Multiset.card t + 1) := by rw [Nat.sub_zero, ← pow_succ']
    · have hexp : Multiset.card t + 1 - (j + 1) = Multiset.card t - j := by omega
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hexp]
      refine v.map_sub_le (ih hta j) ?_
      rw [map_mul]
      by_cases hj : j + 1 ≤ Multiset.card t
      · calc v a * v (((t.map fun a => X - C a).prod).coeff (j + 1))
            ≤ B * B ^ (Multiset.card t - (j + 1)) := mul_le_mul' haB (ih hta (j + 1))
          _ = B ^ (Multiset.card t - (j + 1) + 1) := by rw [← pow_succ']
          _ = B ^ (Multiset.card t - j) := by congr 1; omega
      · have hzero : ((t.map fun a => X - C a).prod).coeff (j + 1) = 0 := by
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
          omega
        rw [hzero, v.map_zero, mul_zero]
        exact zero_le


private lemma valuation_coeff_multisetProd_X_sub_C_lt {t : Multiset K} {B : Γ₀}
    (hB0 : B ≠ 0) (ht : ∀ r ∈ t, v r < B) {i : ℕ} (hi : i < Multiset.card t) :
    v (((t.map fun a => X - C a).prod).coeff i) < B ^ (Multiset.card t - i) := by
  induction t using Multiset.induction generalizing i with
  | empty => simp at hi
  | cons a t ih =>
    have hta : ∀ r ∈ t, v r < B := fun r hr => ht r (Multiset.mem_cons_of_mem hr)
    have htale : ∀ r ∈ t, v r ≤ B := fun r hr => (hta r hr).le
    have haB : v a < B := ht a (Multiset.mem_cons_self a t)
    rw [Multiset.card_cons] at hi
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rcases i with _ | j
    · rw [Polynomial.mul_coeff_zero]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
      rw [map_mul, v.map_neg, Nat.sub_zero]
      calc v a * v (((t.map fun a => X - C a).prod).coeff 0)
          < B * B ^ (Multiset.card t - 0) :=
            slope_mul_lt_mul_of_lt_of_le haB
              (valuation_coeff_multisetProd_X_sub_C_le v htale 0)
              (pow_ne_zero _ hB0)
        _ = B ^ (Multiset.card t + 1) := by rw [Nat.sub_zero, ← pow_succ']
    · have hj : j < Multiset.card t := by omega
      have hexp : Multiset.card t + 1 - (j + 1) = Multiset.card t - j := by omega
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hexp]
      refine lt_of_le_of_lt (v.map_sub _ _) (max_lt ?_ ?_)
      · exact ih hta hj
      · rw [map_mul]
        calc v a * v (((t.map fun a => X - C a).prod).coeff (j + 1))
            < B * B ^ (Multiset.card t - (j + 1)) :=
              slope_mul_lt_mul_of_lt_of_le haB
                (valuation_coeff_multisetProd_X_sub_C_le v htale (j + 1))
                (pow_ne_zero _ hB0)
          _ = B ^ (Multiset.card t - (j + 1) + 1) := by rw [← pow_succ']
          _ = B ^ (Multiset.card t - j) := by congr 1; omega


private lemma valuation_coeff_zero_multisetProd_X_sub_C (t : Multiset K) :
    v (((t.map fun a => X - C a).prod).coeff 0) = (t.map fun a => v a).prod := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map,
    map_multiset_prod (v : Valuation K Γ₀), Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    zero_sub, v.map_neg]


/-- 全根が付値環の外にあり、係数が単元か最高係数以下なら、全根は同じ傾きを持つ。
根rについてv(r)^degree・v(leadingCoeff)=1となる。最大付値の根群と残りを分離して証明する。 -/
theorem root_pow_natDegree_mul_leadingCoeff_eq_one {f : Polynomial K}
    (hsplit : Multiset.card f.roots = f.natDegree)
    (hcoeff : ∀ j, v (f.coeff j) ≤ 1)
    (hgap : ∀ j, v (f.coeff j) = 1 ∨ v (f.coeff j) ≤ v f.leadingCoeff)
    (hroots : ∀ r ∈ f.roots, 1 < v r)
    {r : K} (hr : r ∈ f.roots) :
    v (r ^ f.natDegree * f.leadingCoeff) = 1 := by
  classical
  have hf : f ≠ 0 := fun h => by simp [h] at hr
  have hπ0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hvπ0 : v f.leadingCoeff ≠ 0 := (Valuation.ne_zero_iff v).mpr hπ0
  have htne : f.roots ≠ 0 := fun h => by simp [h] at hr
  have hd1 : 1 ≤ f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exact absurd (Multiset.card_eq_zero.mp (hsplit.trans h0)) htne
    · exact h
  have hfact : Polynomial.C f.leadingCoeff * (f.roots.map fun a => X - C a).prod = f :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  obtain ⟨r₀, hr₀f, hr₀max⟩ : ∃ r₀ ∈ f.roots.toFinset, ∀ a ∈ f.roots.toFinset, v a ≤ v r₀ :=
    f.roots.toFinset.exists_max_image v (Multiset.toFinset_nonempty.mpr htne)
  have hr₀t : r₀ ∈ f.roots := Multiset.mem_toFinset.mp hr₀f
  have hmax : ∀ a ∈ f.roots, v a ≤ v r₀ := fun a ha =>
    hr₀max a (Multiset.mem_toFinset.mpr ha)
  have hM1 : 1 < v r₀ := hroots r₀ hr₀t
  have hM0 : v r₀ ≠ 0 := (zero_lt_one.trans hM1).ne'
  set u : Multiset K := f.roots.filter (fun a => v a = v r₀) with hu
  set w : Multiset K := f.roots.filter (fun a => ¬ v a = v r₀) with hw
  have huw : u + w = f.roots := Multiset.filter_add_not _ f.roots
  have hsw : Multiset.card u + Multiset.card w = f.natDegree := by
    rw [← Multiset.card_add, huw, hsplit]
  have hr₀u : r₀ ∈ u := Multiset.mem_filter.mpr ⟨hr₀t, rfl⟩
  have hs1 : Multiset.card u ≠ 0 := fun h =>
    absurd (Multiset.card_eq_zero.mp h ▸ hr₀u) (Multiset.notMem_zero r₀)
  have humem : ∀ a ∈ u, v a = v r₀ := fun a ha => (Multiset.mem_filter.mp ha).2
  have hwmem_lt : ∀ a ∈ w, v a < v r₀ := fun a ha =>
    lt_of_le_of_ne (hmax a (Multiset.mem_filter.mp ha).1) (Multiset.mem_filter.mp ha).2
  have hwmem_root : ∀ a ∈ w, a ∈ f.roots := fun a ha => (Multiset.mem_filter.mp ha).1
  have hgk : (f.roots.map fun a => X - C a).prod
      = (u.map fun a => X - C a).prod * (w.map fun a => X - C a).prod := by
    rw [← Multiset.prod_add, ← Multiset.map_add, huw]
  have hkmonic : ((w.map fun a => X - C a).prod).Monic :=
    Polynomial.monic_multisetProd_X_sub_C w
  have hkdeg : ((w.map fun a => X - C a).prod).natDegree = Multiset.card w :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card w
  have hgdeg : ((u.map fun a => X - C a).prod).natDegree = Multiset.card u :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card u
  have hg0 : v (((u.map fun a => X - C a).prod).coeff 0)
      = v r₀ ^ Multiset.card u := by
    rw [valuation_coeff_zero_multisetProd_X_sub_C v u]
    have hrep : (u.map fun a => v a) = Multiset.replicate (Multiset.card u) (v r₀) :=
      Multiset.eq_replicate.mpr
        ⟨by rw [Multiset.card_map], fun b hb => by
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
          exact humem a ha⟩
    rw [hrep, Multiset.prod_replicate]
  have hcoeff_f : ∀ j, f.coeff j
      = f.leadingCoeff
        * ((u.map fun a => X - C a).prod * (w.map fun a => X - C a).prod).coeff j := by
    intro j
    conv_lhs => rw [← hfact, hgk]
    rw [Polynomial.coeff_C_mul]
  have hkey₀ : v (f.coeff (f.natDegree - Multiset.card u))
      = v f.leadingCoeff * v r₀ ^ Multiset.card u := by
    rw [hcoeff_f, map_mul]
    congr 1
    rw [Polynomial.coeff_mul]
    have hmem : ((0 : ℕ), f.natDegree - Multiset.card u)
        ∈ Finset.HasAntidiagonal.antidiagonal (f.natDegree - Multiset.card u) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add _)
    rw [← Finset.add_sum_erase _ _ hmem]
    have hterm : v ((((u.map fun a => X - C a).prod).coeff 0)
        * (((w.map fun a => X - C a).prod).coeff (f.natDegree - Multiset.card u)))
        = v r₀ ^ Multiset.card u := by
      have hwdeg : Multiset.card w = f.natDegree - Multiset.card u := by omega
      have htop : (((w.map fun a => X - C a).prod).coeff (f.natDegree - Multiset.card u)) = 1 := by
        rw [← hwdeg, ← hkdeg]
        exact hkmonic.coeff_natDegree
      rw [htop, mul_one, hg0]
    have hrest : v (∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal (f.natDegree - Multiset.card u)).erase
        (0, f.natDegree - Multiset.card u),
        (((u.map fun a => X - C a).prod).coeff ij.1)
          * (((w.map fun a => X - C a).prod).coeff ij.2))
        < v r₀ ^ Multiset.card u := by
      refine Valuation.map_sum_lt v (pow_ne_zero _ hM0) fun ij hij => ?_
      obtain ⟨hij_ne, hij_mem⟩ := Finset.mem_erase.mp hij
      have hij_sum : ij.1 + ij.2 = f.natDegree - Multiset.card u :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij_mem
      have hij1 : ij.1 ≠ 0 := by
        intro h0
        exact hij_ne (Prod.ext h0 (by omega))
      rw [map_mul]
      by_cases hbig : Multiset.card u < ij.1
      · have : (((u.map fun a => X - C a).prod).coeff ij.1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; exact hbig)
        rw [this, v.map_zero, zero_mul]
        exact zero_lt_iff.mpr (pow_ne_zero _ hM0)
      · rw [not_lt] at hbig
        have hwdeg : Multiset.card w = f.natDegree - Multiset.card u := by omega
        have hij2 : ij.2 < Multiset.card w := by omega
        have h1 : v (((u.map fun a => X - C a).prod).coeff ij.1)
            ≤ v r₀ ^ (Multiset.card u - ij.1) :=
          valuation_coeff_multisetProd_X_sub_C_le v (fun a ha => (humem a ha).le) ij.1
        have h2 : v (((w.map fun a => X - C a).prod).coeff ij.2)
            < v r₀ ^ (Multiset.card w - ij.2) :=
          valuation_coeff_multisetProd_X_sub_C_lt v hM0 hwmem_lt hij2
        calc v (((u.map fun a => X - C a).prod).coeff ij.1)
              * v (((w.map fun a => X - C a).prod).coeff ij.2)
            < v r₀ ^ (Multiset.card u - ij.1) * v r₀ ^ (Multiset.card w - ij.2) :=
              slope_mul_lt_mul_of_le_of_lt h1 h2 (pow_ne_zero _ hM0)
          _ = v r₀ ^ (Multiset.card u - ij.1 + (Multiset.card w - ij.2)) := (pow_add _ _ _).symm
          _ = v r₀ ^ Multiset.card u := by congr 1; omega
    rw [Valuation.map_add_eq_of_lt_left v (hterm ▸ hrest), hterm]
  have hkey : v f.leadingCoeff * v r₀ ^ Multiset.card u = 1 := by
    rcases hgap (f.natDegree - Multiset.card u) with h1 | h2
    · rw [← hkey₀, h1]
    · exfalso
      rw [hkey₀] at h2
      have hcancel : v r₀ ^ Multiset.card u ≤ 1 := by
        have h3 := mul_le_mul_right h2 (v f.leadingCoeff)⁻¹
        rwa [← mul_assoc, inv_mul_cancel₀ hvπ0, one_mul] at h3
      exact absurd hcancel (not_le.mpr (slope_one_lt_pow hM1 hs1))
  have hwzero : w = 0 := by
    by_contra hwne
    have hconst : v (f.coeff 0) = (w.map fun a => v a).prod := by
      rw [hcoeff_f, map_mul, Polynomial.mul_coeff_zero, map_mul, hg0,
        valuation_coeff_zero_multisetProd_X_sub_C v w, ← mul_assoc, hkey, one_mul]
    have hgt : 1 < (w.map fun a => v a).prod := by
      refine slope_one_lt_prod (by simpa using hwne) fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      exact hroots a (hwmem_root a ha)
    exact absurd (hconst ▸ hcoeff 0) (not_le.mpr hgt)
  have hsd : Multiset.card u = f.natDegree := by
    have : Multiset.card w = 0 := by rw [hwzero, Multiset.card_zero]
    omega
  have hru : r ∈ u := by
    have : r ∈ u + w := huw ▸ hr
    rwa [hwzero, add_zero] at this
  rw [map_mul, v.map_pow, humem r hru, ← hsd, mul_comm]
  exact hkey

end DkMath.Lib.Algebra.SingleSlopeRoot
