/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNPhaseFactorization
import DkMath.Lib.NumberTheory.PrincipalIdealPower
import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

#print "file: DkMath.Lib.NumberTheory.CosmicIdealBridge"

/-!
# 多項式からイデアルへ、そして元へ

教科書的な順序で GN の因子を追跡する。
1. 元の積を主イデアルの積へ写す。
2. 二つの因子を引き、共通素イデアルが分岐因子 `ζ - 1` を含むと示す。
3. 分岐因子と gap の互いに素性から、因子イデアルの互いに素性を得る。
4. Dedekind 整域のイデアル分解で冪を抽出する。
5. 類群の torsion を消し、単元を保持して元へ戻す。

第 3 段階の仮定は分岐する場合には使えない。したがって最後の定理は
非分岐側の構造定理であり、Kummer の単元補題や無限降下を含まない。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators nonZeroDivisors
open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

/-- 任意の GTail 切断も、prefix を引いた剰余を介してイデアルに接続する。
加法分割を直接イデアル和に置き換えるのでなく、剰余の因数分解
`remainder = x^r * GTail d r x u` を使う。これは円分ノルム表示とは別の、
全切断に有効な主イデアルの乗法等式である。 -/
theorem span_tail_remainder
    {R : Type*} [CommRing R] (d r : ℕ) (x u : R) (hr : r ≤ d) :
    Ideal.span ({(x + u) ^ d -
      ∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j)} : Set R) =
      Ideal.span ({x} : Set R) ^ r * Ideal.span ({GTail d r x u} : Set R) := by
  rw [add_pow_eq_prefix_add_xpow_mul_GTail d r x u hr, add_sub_cancel_left,
    Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]

/-- 主イデアル化は有限積を保存する。加法の保存は使わない。 -/
theorem span_singleton_prod_eq_prod_span
    {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ∏ i ∈ s, Ideal.span ({f i} : Set R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      ← Ideal.span_singleton_mul_span_singleton, ih]

/-- GN の非自明な円分因子を、そのまま主イデアルの積に輸送する。
因子分解は形式変数での等式なので `x = 0` も許される。 -/
theorem span_GTail_eq_prod_phase_span
    {R : Type*} [CommRing R] [IsDomain R]
    {d : ℕ} {ζ : R} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) (x u : R) :
    Ideal.span ({GTail d 1 x u} : Set R) =
      ∏ i ∈ (Finset.range d).erase 0,
        Ideal.span ({x + (1 - ζ ^ i) * u} : Set R) := by
  classical
  rw [GN_eq_nontrivial_phase_prod_range hd hζ, span_singleton_prod_eq_prod_span]

/-- `x GN = c^p` を全ての因子イデアルの積へ移す。
添字 0 の因子は gap `x` 自身である。 -/
theorem prod_phase_span_eq_span_pow
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u c : R} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p)
    (heq : x * GTail p 1 x u = c ^ p) :
    (∏ i ∈ Finset.range p, Ideal.span ({x + (1 - ζ ^ i) * u} : Set R)) =
      Ideal.span ({c} : Set R) ^ p := by
  classical
  rw [← span_singleton_prod_eq_prod_span, Ideal.span_singleton_pow]
  congr 1
  apply congrArg Set.singleton
  rw [← focused_pow_sub_pow_eq_prod_range hp hζ,
    add_pow_eq_mul_GTail_one_add_gap, add_sub_cancel_right, heq]

/-- 素数次数の異なる因子が同じ素イデアルに入ると、
その素イデアルは `ζ - 1` または `u` を含む。
差は `(ζ^j - ζ^i)u` であり、根の差は `ζ - 1` と同伴である。 -/
theorem common_prime_contains_ramified_or_parameter
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j)
    {P : Ideal R} (hP : P.IsPrime)
    (hfi : x + (1 - ζ ^ i) * u ∈ P) (hfj : x + (1 - ζ ^ j) * u ∈ P) :
    ζ - 1 ∈ P ∨ u ∈ P := by
  have hroot (k : ℕ) : ζ ^ k ∈ Polynomial.nthRootsFinset p (1 : R) := by
    rw [Polynomial.mem_nthRootsFinset hp.pos, ← pow_mul, mul_comm k p,
      pow_mul, hζ.pow_eq_one, one_pow]
  have hassoc : Associated (ζ ^ j - ζ ^ i) (ζ - 1) :=
    (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp
      (hroot j) (hroot i) (fun h => hij (hζ.pow_inj hi hj h.symm))).symm
  have hd : (ζ ^ j - ζ ^ i) * u ∈ P := by
    convert P.sub_mem hfi hfj using 1
    ring
  obtain ⟨v, hv⟩ := hassoc.mul_right u
  have hm := P.mul_mem_right (v : R) hd
  rw [hv] at hm
  exact hP.mem_or_mem hm

private theorem not_both_mem_prime_of_isCoprime
    {R : Type*} [CommRing R] {a b : R} (hab : IsCoprime a b)
    {P : Ideal R} (hP : P.IsPrime) (ha : a ∈ P) (hb : b ∈ P) : False := by
  obtain ⟨r, s, hrs⟩ := hab
  have h := P.add_mem (P.mul_mem_left r ha) (P.mul_mem_left s hb)
  rw [hrs] at h
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)

/-- 原始性 `IsCoprime x u` が parameter の共通因子を除く。
よって残る共通素イデアルは必ず分岐因子 `ζ - 1` を含む。 -/
theorem common_prime_contains_ramified
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hxu : IsCoprime x u)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j)
    {P : Ideal R} (hP : P.IsPrime)
    (hfi : x + (1 - ζ ^ i) * u ∈ P) (hfj : x + (1 - ζ ^ j) * u ∈ P) :
    ζ - 1 ∈ P := by
  rcases common_prime_contains_ramified_or_parameter hp hζ hi hj hij hP hfi hfj with h | hu
  · exact h
  · have hx : x ∈ P := by
      simpa using P.sub_mem hfi (P.mul_mem_left (1 - ζ ^ i) hu)
    exact (not_both_mem_prime_of_isCoprime hxu hP hx hu).elim

/-- 分岐因子が gap と互いに素なら、円分因子イデアルは対ごとに互いに素。
`ζ - 1 ∈ P` なら `1 - ζ^i ∈ P` なので、共通素イデアルは gap も含み、
仮定 `IsCoprime x (ζ - 1)` と矛盾する。 -/
theorem phase_spans_pairwise_isCoprime
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ x u : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hxu : IsCoprime x u) (hxζ : IsCoprime x (ζ - 1)) :
    Set.Pairwise (↑(Finset.range p)) (fun i j =>
      IsCoprime (Ideal.span ({x + (1 - ζ ^ i) * u} : Set R))
        (Ideal.span ({x + (1 - ζ ^ j) * u} : Set R))) := by
  intro i hi j hj hij
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hleI hleJ hP
  have hfi := hleI (Ideal.subset_span (Set.mem_singleton _))
  have hfj := hleJ (Ideal.subset_span (Set.mem_singleton _))
  have hζP := common_prime_contains_ramified hp hζ hxu
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij hP hfi hfj
  have hpow : ζ ^ i - 1 ∈ P := by
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow ζ (1 : R) i
    rw [one_pow] at ht
    rw [ht]
    exact P.mul_mem_right t hζP
  have hx : x ∈ P := by
    have h := P.add_mem hfi (P.mul_mem_right u hpow)
    convert h using 1
    ring
  exact not_both_mem_prime_of_isCoprime hxζ hP hx hζP

/-- イデアルの冪抽出と類群による主イデアル化を連結する汎用補題。
有限積の各因子は、非零性・互いに素性・類群条件のもとで単元倍の冪になる。
単元は捨てず、イデアル根と生成元も証明結果に残す。 -/
theorem exists_ideal_and_unit_pow_of_coprime_prod
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {ι : Type*} {s : Finset ι} {f : ι → R} {c : R} {p : ℕ}
    (hp : 0 < p) (hc : c ≠ 0)
    (hprod : (∏ i ∈ s, Ideal.span ({f i} : Set R)) = Ideal.span ({c} : Set R) ^ p)
    (hcop : Set.Pairwise (↑s) (fun i j =>
      IsCoprime (Ideal.span ({f i} : Set R)) (Ideal.span ({f j} : Set R))))
    (hfree : classGroupPTorsionFreeAt R p) {i : ι} (hi : i ∈ s) :
    ∃ (I : Ideal R) (ε γ : R), I ≠ ⊥ ∧
      Ideal.span ({f i} : Set R) = I ^ p ∧ IsUnit ε ∧
      Ideal.span ({γ} : Set R) = I ∧ f i = ε * γ ^ p := by
  classical
  have hm : Ideal.span ({f i} : Set R) *
      (∏ j ∈ s.erase i, Ideal.span ({f j} : Set R)) = Ideal.span ({c} : Set R) ^ p := by
    exact (Finset.mul_prod_erase s (fun j => Ideal.span ({f j} : Set R)) hi).trans hprod
  have hcop' : IsCoprime (Ideal.span ({f i} : Set R))
      (∏ j ∈ s.erase i, Ideal.span ({f j} : Set R)) := by
    apply IsCoprime.prod_right
    intro j hj
    exact hcop hi (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm
  obtain ⟨I, hI⟩ := exists_eq_pow_of_isCoprime_mul_eq_pow hcop' hm
  have hI0 : I ≠ ⊥ := by
    intro hz
    have hc0 : Ideal.span ({c} : Set R) ≠ ⊥ := by
      intro h
      exact hc ((Ideal.span_singleton_eq_bot).mp h)
    rw [hI, hz, Ideal.bot_pow hp.ne', Ideal.bot_mul] at hm
    exact (pow_ne_zero p hc0) hm.symm
  obtain ⟨ε, γ, hε, hγ, heq⟩ :=
    exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI0) hfree hI
  exact ⟨I, ε, γ, hI0, hI, hε, hγ, heq⟩

/-- GN 版 Kummer 構造定理の非分岐部分。
`x GN_p(x,u)=c^p`、原始性、分岐因子との互いに素性、および類群の
`p`-torsion 消滅から、各円分因子を `ε γ^p` に復元する。
これは FLT の最終矛盾ではない。単元の合同条件と分岐側の降下は別の課題である。 -/
theorem GN_kummer_structure_of_unramified
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : ℕ} {ζ x u c : R} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hc : c ≠ 0) (heq : x * GTail p 1 x u = c ^ p)
    (hxu : IsCoprime x u) (hxζ : IsCoprime x (ζ - 1))
    (hfree : classGroupPTorsionFreeAt R p) {i : ℕ} (hi : i < p) :
    ∃ (I : Ideal R) (ε γ : R), I ≠ ⊥ ∧
      Ideal.span ({x + (1 - ζ ^ i) * u} : Set R) = I ^ p ∧ IsUnit ε ∧
      Ideal.span ({γ} : Set R) = I ∧ x + (1 - ζ ^ i) * u = ε * γ ^ p := by
  exact exists_ideal_and_unit_pow_of_coprime_prod hp.pos hc
    (prod_phase_span_eq_span_pow hp.pos hζ heq)
    (phase_spans_pairwise_isCoprime hp hζ hxu hxζ) hfree (Finset.mem_range.mpr hi)

end DkMath.Lib.NumberTheory
