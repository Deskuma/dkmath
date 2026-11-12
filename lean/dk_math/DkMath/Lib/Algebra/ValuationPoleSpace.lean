/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TranscendentalFiniteDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

#print "file: DkMath.Lib.Algebra.ValuationPoleSpace"

/-!
# 一変数関数体の極のフィルトレーション

[DkMath.Lib] 代数閉体k上の一変数関数体の付値では、同じ大きさの二項の最高項を
kのスカラーで相殺できる。一般の因子や曲線のモデルを仮定せず、超越元交換と
k上の多項式の一次分解から示す。これが一段ごとの次元増分を高々1にする。
-/
namespace DkMath.Lib.Algebra.ValuationPoleSpace
open Polynomial IntermediateField WithZero
variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]

/-- [DkMath.Lib] 定数に自明な一変数関数体付値の剰余は係数体で尽くされる。
zの値が1なら、ある定数cを引くと値が1未満になる。
全ての差が値1ならk(z)上付値が自明となり、極を持つxの代数性に反する。 -/
theorem exists_const_sub_lt (v : Valuation F ℤᵐ⁰)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (x : F) (hx : Transcendental k x) [FiniteDimensional k⟮x⟯ F]
    (hxv : 1 < v x) (z : F) (hz : v z = 1) :
    ∃ c : k, v (z - algebraMap k F c) < 1 := by
  classical
  by_contra! hno
  have hlin : ∀ c : k, v (z - algebraMap k F c) = 1 := by
    intro c
    refine le_antisymm ((v.map_sub _ _).trans (max_le (le_of_eq hz) ?_)) (hno c)
    by_cases hc : c = 0
    · simp [hc]
    · exact (hconst c hc).le
  have hpoly : ∀ p : k[X], p ≠ 0 → v (aeval z p) = 1 := by
    intro p hp
    rw [(IsAlgClosed.splits p).eq_prod_roots, map_mul, aeval_C, map_mul,
      hconst _ (leadingCoeff_ne_zero.mpr hp), one_mul]
    have hm : ∀ s : Multiset k, v (aeval z ((s.map fun c => X - C c).prod)) = 1 := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons c s ih => simp only [Multiset.map_cons, Multiset.prod_cons, map_mul,
          map_sub, aeval_X, aeval_C, hlin, ih, one_mul]
    exact hm p.roots
  have hztrans : Transcendental k z := by
    apply transcendental_iff.mpr
    intro p hp
    by_contra hne
    have hv := hpoly p hne
    rw [hp, map_zero] at hv
    exact zero_ne_one hv
  have htriv : ∀ a : k⟮z⟯, a ≠ 0 → v (a : F) = 1 := by
    intro a ha
    obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff k (a : F)).mp a.2
    have hp : p ≠ 0 := by rintro rfl; simp only [map_zero, zero_div] at he; exact ha (Subtype.ext he)
    have hq : q ≠ 0 := by rintro rfl; simp only [map_zero, div_zero] at he; exact ha (Subtype.ext he)
    rw [he, map_div₀, hpoly p hp, hpoly q hq, div_self one_ne_zero]
  let : v.IsTrivialOn k⟮z⟯ := ⟨htriv⟩
  have hxalg : IsAlgebraic k⟮z⟯ x :=
    isAlgebraic_adjoin_iff.mpr (.adjoin_singleton hx hztrans
      (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic z)))
  exact (v.transcendental_of_ne_one k⟮z⟯ x
    (v.ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hxv))) (ne_of_gt hxv)) hxalg

/-- [DkMath.Lib] 同じ非零付値を持つ二関数の最高項を、係数体のスカラー倍で相殺する。 -/
theorem exists_sub_smul_lt (v : Valuation F ℤᵐ⁰)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (x : F) (hx : Transcendental k x) [FiniteDimensional k⟮x⟯ F]
    (hxv : 1 < v x) {f g : F} (hg : g ≠ 0) (he : v f = v g) :
    ∃ c : k, v (f - c • g) < v g := by
  have hgval : v g ≠ 0 := v.ne_zero_iff.mpr hg
  have hquot : v (f / g) = 1 := by rw [map_div₀, he, div_self hgval]
  obtain ⟨c, hc⟩ := exists_const_sub_lt v hconst x hx hxv (f / g) hquot
  refine ⟨c, ?_⟩
  have heq : f - c • g = (f / g - algebraMap k F c) * g := by
    rw [Algebra.smul_def]; field_simp
  rw [heq, map_mul]
  simpa using mul_lt_mul_of_pos_right hc (v.pos_iff.mpr hg)

omit [IsAlgClosed k] in
/-- [DkMath.Lib] fの値がexp(d)なら、k(f)の非零元の値の指数はdの整数倍。
分子分母の最高次数の差を実際に計算し、極位数の合同類を次数の下界へ使えるようにする。 -/
theorem value_adjoin_simple (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1)
    (f : F) (d : ℕ) (hd : 0 < d) (hf : v f = exp (d : ℤ))
    (a : k⟮f⟯) (ha : a ≠ 0) : ∃ m : ℤ, v (a : F) = exp ((d : ℤ) * m) := by
  obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff k (a : F)).mp a.2
  have hp : p ≠ 0 := by rintro rfl; simp only [map_zero, zero_div] at he; exact ha (Subtype.ext he)
  have hq : q ≠ 0 := by rintro rfl; simp only [map_zero, div_zero] at he; exact ha (Subtype.ext he)
  have hpos : 1 < v f := by rw [hf, ← exp_zero, exp_lt_exp]; exact_mod_cast hd
  have hv : ∀ p : k[X], p ≠ 0 → v (aeval f p) = exp ((d : ℤ) * p.natDegree) := by
    intro p hp
    let : v.IsTrivialOn k := ⟨hc⟩
    rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X f hpos hp,
      hf, ← exp_nsmul, nsmul_eq_mul, mul_comm]
  refine ⟨(p.natDegree : ℤ) - q.natDegree, ?_⟩
  rw [he, map_div₀, hv p hp, hv q hq, ← exp_sub]
  congr 1
  ring

omit [IsAlgClosed k] in
/-- [DkMath.Lib] 正則なfから作るk[f]上の整元は同じ付値で正則である。
付値環の整閉性を使い、整基底が核の外で新しい極を作らないことを保証する。 -/
theorem le_one_of_isIntegral_adjoin {A : Type*} [Field A] [Algebra k A]
    [Algebra A F] [IsScalarTower k A F] (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1) (f : A)
    (hf : v (algebraMap A F f) ≤ 1) (g : F)
    (hg : IsIntegral (Algebra.adjoin k {f}) g) : v g ≤ 1 := by
  let V : Subalgebra k F :=
    { v.valuationSubring.toSubring with
      algebraMap_mem' c := hc c }
  have hle : (Algebra.adjoin k {f}).map (IsScalarTower.toAlgHom k A F) ≤ V := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ hf
  have hmem : ∀ a : Algebra.adjoin k {f}, algebraMap (Algebra.adjoin k {f}) F a ∈
      v.valuationSubring := fun a => hle ⟨a.val, a.property, rfl⟩
  let φ : Algebra.adjoin k {f} →+* v.valuationSubring :=
    (algebraMap (Algebra.adjoin k {f}) F).codRestrict _ hmem
  have hint : IsIntegral v.valuationSubring g :=
    hg.map_of_comp_eq φ (RingHom.id F) (by ext a; rfl)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.valuationSubring) (K := F)).mp hint
  rw [← ha]
  exact a.property

/-- [DkMath.Lib] 整数値付値の一段未満は、直前の整数段以下である。零関数も許す。 -/
theorem le_exp_of_lt_exp_succ (v : Valuation F ℤᵐ⁰) (f : F) (n : ℕ)
    (h : v f < exp ((n + 1 : ℕ) : ℤ)) : v f ≤ exp (n : ℤ) := by
  by_cases hf : v f = 0
  · rw [hf]; exact zero_le
  · rw [← exp_log hf, exp_lt_exp] at h
    rw [← exp_log hf, exp_le_exp]
    exact Int.lt_add_one_iff.mp (by simpa using h)

/-- [DkMath.Lib] 部分代数Rの中で、指定付値の極が高々nの関数空間。
Rは他の点での正則性・対称性などを保持するための実際の部分代数である。 -/
noncomputable def poleSpace (R : Subalgebra k F) (v : Valuation F ℤᵐ⁰)
    (hconst : ∀ c : k, v (algebraMap k F c) ≤ 1) (n : ℕ) : Submodule k F where
  carrier := {f | f ∈ R ∧ v f ≤ exp (n : ℤ)}
  zero_mem' := ⟨R.zero_mem, by simp⟩
  add_mem' hf hg := ⟨R.add_mem hf.1 hg.1, (v.map_add _ _).trans (max_le hf.2 hg.2)⟩
  smul_mem' c f hf := ⟨R.smul_mem hf.1 c, by
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul' (hconst c) hf.2).trans_eq (one_mul _)⟩

omit [IsAlgClosed k] in
/-- [DkMath.Lib] 極の上界を緩めると空間は包含される。 -/
theorem poleSpace_mono (R : Subalgebra k F) (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    poleSpace R v hc m ≤ poleSpace R v hc n := by
  intro f hf
  exact ⟨hf.1, hf.2.trans (exp_le_exp.mpr (by exact_mod_cast hmn))⟩

omit [IsAlgClosed k] in
/-- [DkMath.Lib] 最高項を一つずつ消去し、極が高々nの空間の次元をn+1以下に抑える。
極のないRの元が定数であることと、同じ付値の最高項のスカラー相殺を入力とする。
一般Riemann–Roch定理ではなく、この二性質からの有限次元性の構成である。 -/
theorem finiteDimensional_finrank_poleSpace (R : Subalgebra k F) (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1)
    (hregular : ∀ f ∈ R, v f ≤ 1 → ∃ c : k, f = algebraMap k F c)
    (hcancel : ∀ {f g : F}, g ≠ 0 → v f = v g → ∃ c : k, v (f - c • g) < v g)
    (n : ℕ) : FiniteDimensional k (poleSpace R v hc n) ∧
      Module.finrank k (poleSpace R v hc n) ≤ n + 1 := by
  classical
  induction n with
  | zero =>
    have hle : poleSpace R v hc 0 ≤ k ∙ (1 : F) := by
      intro f hf
      obtain ⟨c, he⟩ := hregular f hf.1 (by simpa using hf.2)
      rw [he]
      simpa only [Algebra.smul_def, mul_one] using
        (Submodule.smul_mem (k ∙ (1 : F)) c (Submodule.mem_span_singleton_self 1))
    let := Submodule.finiteDimensional_of_le hle
    refine ⟨inferInstance, ?_⟩
    exact (Submodule.finrank_mono hle).trans_eq (finrank_span_singleton one_ne_zero)
  | succ n ih =>
    let := ih.1
    by_cases he : poleSpace R v hc (n + 1) ≤ poleSpace R v hc n
    · let := Submodule.finiteDimensional_of_le he
      exact ⟨inferInstance, (Submodule.finrank_mono he).trans (by omega)⟩
    · obtain ⟨g, hg, hgn⟩ := SetLike.not_le_iff_exists.mp he
      have hg0 : g ≠ 0 := by rintro rfl; exact hgn (Submodule.zero_mem _)
      have hgval : v g = exp ((n + 1 : ℕ) : ℤ) := by
        apply le_antisymm hg.2
        by_contra! hlt
        exact hgn ⟨hg.1, le_exp_of_lt_exp_succ v g n hlt⟩
      have hle : poleSpace R v hc (n + 1) ≤ poleSpace R v hc n ⊔ k ∙ g := by
        intro f hf
        by_cases hfn : f ∈ poleSpace R v hc n
        · exact Submodule.mem_sup_left hfn
        · have hfval : v f = v g := by
            rw [hgval]
            apply le_antisymm hf.2
            by_contra! hlt
            exact hfn ⟨hf.1, le_exp_of_lt_exp_succ v f n hlt⟩
          obtain ⟨c, hsub⟩ := hcancel hg0 hfval
          have hs : f - c • g ∈ poleSpace R v hc n :=
            ⟨R.sub_mem hf.1 (R.smul_mem hg.1 c),
              le_exp_of_lt_exp_succ v _ n (by rwa [hgval] at hsub)⟩
          have hcg : c • g ∈ k ∙ g :=
            Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
          exact Submodule.mem_sup.mpr ⟨f - c • g, hs, c • g, hcg, sub_add_cancel _ _⟩
      let := Submodule.finiteDimensional_of_le hle
      refine ⟨inferInstance, ?_⟩
      calc Module.finrank k (poleSpace R v hc (n + 1))
          ≤ Module.finrank k (poleSpace R v hc n ⊔ k ∙ g : Submodule k F) :=
            Submodule.finrank_mono hle
        _ ≤ Module.finrank k (poleSpace R v hc n) + Module.finrank k (k ∙ g) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ n + 1 + 1 := by rw [finrank_span_singleton hg0]; omega

end DkMath.Lib.Algebra.ValuationPoleSpace
