/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.ValuationPoleSpace
import Mathlib.FieldTheory.RatFunc.AsPolynomial

#print "file: DkMath.Lib.Algebra.ValuationRationalPolynomial"

/-!
# 有限極を持たない有理式は多項式である

[DkMath.Lib] fの全ての有限値cを零点で検出できれば、fに関する有理式の非定数分母は
どこかに極を生む。既約分子分母のBezout等式が、見掛けの零点の相殺を排除する。
係数体の代数閉性と実際の零点検出を明示し、単なる次数台帳にしない。
-/
namespace DkMath.Lib.Algebra.ValuationRationalPolynomial
open Polynomial IntermediateField WithZero
variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]

omit [IsAlgClosed k] in
/-- [DkMath.Lib] 正則な係数と代入元の多項式評価は正則。 -/
theorem aeval_le_one (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1) (f : F) (hf : v f ≤ 1) (p : k[X]) :
    v (aeval f p) ≤ 1 := by
  let V : Subalgebra k F := { v.valuationSubring.toSubring with algebraMap_mem' c := hc c }
  have hle : Algebra.adjoin k {f} ≤ V := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hf)
  apply hle
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p, rfl⟩

omit [IsAlgClosed k] in
/-- [DkMath.Lib] 超越元の単純体の実際の元は、互いに素な多項式の比で書ける。 -/
theorem exists_coprime_fraction (f : F) (hf : Transcendental k f) {g : F} (hg : g ∈ k⟮f⟯) :
    ∃ p q : k[X], IsCoprime p q ∧ q ≠ 0 ∧ g = aeval f p / aeval f q := by
  let e := RatFunc.algEquivOfTranscendental f hf
  let r := e.symm ⟨g, hg⟩
  refine ⟨r.num, r.denom, r.isCoprime_num_denom, r.denom_ne_zero, ?_⟩
  calc g = (e r : F) := (congrArg Subtype.val (e.apply_symm_apply ⟨g, hg⟩)).symm
    _ = _ := RatFunc.algEquivOfTranscendental_apply f hf r

/-- [DkMath.Lib] fの有限値を付値で検出でき、g∈k(f)が全ての検出点で正則ならgはfの多項式。
分母の根cでf−cの値が1未満となる場所を使い、Bezoutで分子分母の同時消滅を排除する。 -/
theorem exists_polynomial_of_regular {ι : Type*} (v : ι → Valuation F ℤᵐ⁰)
    (hc : ∀ i c, v i (algebraMap k F c) ≤ 1)
    (f : F) (hf : Transcendental k f)
    (hzero : ∀ c : k, ∃ i, v i f ≤ 1 ∧ v i (f - algebraMap k F c) < 1)
    {g : F} (hg : g ∈ k⟮f⟯) (hgreg : ∀ i, v i g ≤ 1) :
    ∃ p : k[X], g = aeval f p := by
  classical
  obtain ⟨p, q, hpq, hq0, he⟩ := exists_coprime_fraction f hf hg
  have hqeval : aeval f q ≠ 0 := fun h => hq0 ((transcendental_iff.mp hf) q h)
  have hqdeg : q.natDegree = 0 := by
    by_contra hdeg
    obtain ⟨c, hcq⟩ := IsAlgClosed.exists_root q (degree_ne_of_natDegree_ne hdeg)
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hcq : X - C c ∣ q)
    obtain ⟨i, hfi, hfc⟩ := hzero c
    have hqv : v i (aeval f q) < 1 := by
      rw [hr, map_mul, map_sub, aeval_X, aeval_C, map_mul]
      exact lt_of_le_of_lt
        ((mul_le_mul' le_rfl (aeval_le_one (v i) (hc i) f hfi r)).trans_eq (mul_one _)) hfc
    have hpv : v i (aeval f p) < 1 := by
      have hmul : aeval f p = g * aeval f q := (div_eq_iff hqeval).mp he.symm
      rw [hmul, map_mul]
      exact lt_of_le_of_lt ((mul_le_mul' (hgreg i) le_rfl).trans_eq (one_mul _)) hqv
    obtain ⟨a, b, hab⟩ := hpq
    have hv : v i (aeval f (a * p + b * q)) < 1 := by
      rw [map_add, map_mul, map_mul]
      apply lt_of_le_of_lt ((v i).map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact lt_of_le_of_lt ((mul_le_mul' (aeval_le_one (v i) (hc i) f hfi a) le_rfl).trans_eq
          (one_mul _)) hpv
      · rw [map_mul]
        exact lt_of_le_of_lt ((mul_le_mul' (aeval_le_one (v i) (hc i) f hfi b) le_rfl).trans_eq
          (one_mul _)) hqv
    rw [hab, map_one, map_one] at hv
    exact (lt_irrefl _ hv)
  refine ⟨C (q.coeff 0)⁻¹ * p, ?_⟩
  rw [he, Polynomial.eq_C_of_natDegree_eq_zero hqdeg]
  simp only [map_mul, aeval_C, map_inv₀, div_eq_mul_inv, mul_comm, coeff_C_zero]

end DkMath.Lib.Algebra.ValuationRationalPolynomial
