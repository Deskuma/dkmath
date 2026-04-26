/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.RadLogBasic
import DkMath.ABC.SliceAverageBasic

#print "file: DkMath.ABC.SliceDiagonalCounting"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/- small helpers requested by reviewer -/

/-- `Finset.range (X+1)` は `0` から `X` までの閉区間（両端含む）として `Finset.Icc 0 X` と等しいことを示す補題。 -/
lemma range_succ_eq_Icc (X : ℕ) :
  Finset.range (X+1) = Finset.Icc 0 X := by
  ext a
  simp only [Finset.mem_range, Order.lt_add_one_iff, Finset.mem_Icc, zero_le, true_and]


/-- `sliceBadCount_eq_card_filter_Icc` states that the value of `sliceBadCount` for parameters `δ`, `X`, and `b` is equal to the cardinality of the set of `a` in the interval `[0, X]` such that `is_bad_a δ X b a` holds. -/
lemma sliceBadCount_eq_card_filter_Icc (δ : ℝ) (X b : ℕ) :
  sliceBadCount (δ:=δ) X b
    = (Finset.filter (fun a => is_bad_a δ X b a) (Finset.Icc 0 X)).card := by
  -- 定義は range 上のフィルタなので Icc に書き換える
  simp [sliceBadCount, range_succ_eq_Icc X]


/-- diagonal bad-count: number of indices b ≤ X such that is_bad_a δ X b (b - 1). -/
noncomputable def diagCount (δ : ℝ) (X : ℕ) : ℕ :=
  (Finset.filter (fun b => is_bad_a δ X b (b - 1)) (Finset.Icc 0 X)).card


/-- 前寄せ diagonal bad-count：n ≤ X かつ `is_bad_a δ X (n+1) n` の個数 -/
noncomputable def diagCountFwd (δ : ℝ) (X : ℕ) : ℕ :=
  (Finset.filter (fun n => n ≤ X ∧ is_bad_a δ X (n+1) n) (Finset.Icc 0 X)).card


/-- `diagCountFwd_le_diagCount_shift` asserts that for any real number `δ` and natural number `X`, the forward diagonal count at `X` is less than or equal to the diagonal count at `X + 1`. -/
lemma diagCountFwd_le_diagCount_shift (δ : ℝ) (X : ℕ) :
  (diagCountFwd δ X : ℕ) ≤ (diagCount δ (X + 1) : ℕ) := by
  classical
  -- unfold the two counting definitions
  dsimp [diagCountFwd, diagCount]
  -- set S and T for readability
  let S := (Finset.filter (fun n => n ≤ X ∧ is_bad_a δ X (n+1) n) (Finset.Icc 0 X))
  let T := (Finset.filter (fun b => is_bad_a δ (X+1) b (b - 1)) (Finset.Icc 0 (X+1)))
  -- it suffices to embed S into T via the injective map g : n ↦ n+1
  let g : ℕ → ℕ := fun n => n + 1
  have g_inj : Function.Injective g := by
    intro a b h; exact Nat.succ.inj h
  -- show image of S under g is contained in T
  have img_sub : S.image g ⊆ T := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨n, hnS, rfl⟩
    -- unpack membership in S
    rcases Finset.mem_filter.1 hnS with ⟨hnIcc, hn_cond⟩
    rcases Finset.mem_Icc.1 hnIcc with ⟨hn0, hnX⟩
    rcases hn_cond with ⟨hn_le, hbadX⟩
    -- from hbadX : is_bad_a δ X (n+1) n build the loosened version for X+1
    rcases hbadX with ⟨hcop, ha_le, hb_le, hab_le, hBadTriple⟩
    -- inequalities relax when passing from X to X+1
    have ha_le' : n ≤ X + 1 := le_trans ha_le (Nat.le_succ _)
    have hb_le' : n + 1 ≤ X + 1 := le_trans hb_le (Nat.le_succ _)
    have hab_le' : n + (n + 1) ≤ X + 1 := le_trans hab_le (Nat.le_succ _)
    -- membership in Icc 0 (X+1)
    have hmem_Icc : n + 1 ∈ Finset.Icc 0 (X+1) := by
      refine Finset.mem_Icc.2 ?_
      constructor
      · exact Nat.zero_le _
      · exact hb_le'
    -- build new is_bad_a witness
    have hbadX1 : is_bad_a δ (X+1) (n+1) n := ⟨hcop, ha_le', hb_le', hab_le', hBadTriple⟩
    -- finish: (n+1) satisfies target filter predicate
    exact Finset.mem_filter.2 ⟨hmem_Icc, by simpa using hbadX1⟩
  -- cardinality: |S| = |image S| ≤ |T|
  have hcard_image : (S.image g).card = S.card := Finset.card_image_of_injective _ g_inj
  have hcard_le : (S.card : ℕ) ≤ T.card := by
    have := Finset.card_le_card img_sub
    -- rewrite card(image) to card(S)
    simpa [hcard_image]
  simpa [S, T]


/-- 「対角が bad ならそのスライスのカウントは 1 以上」…を ℕ で作る -/
lemma one_le_slice_when_diag
  (δ : ℝ) {X b : ℕ}
  (hb : b ∈ Finset.Icc 0 X) (hbad : is_bad_a δ X b (b - 1)) :
  (1 : ℕ) ≤ sliceBadCount (δ:=δ) X b := by
  classical
  -- (b - 1) が Icc 0 X に入る
  have hb_le : b ≤ X := (Finset.mem_Icc.mp hb).2
  have h0 : 0 ≤ (b - 1) := Nat.zero_le _
  have htop : (b - 1) ≤ X := le_trans (Nat.sub_le _ _) hb_le
  have hmem_Icc : (b - 1) ∈ Finset.Icc 0 X := by
    simp [Finset.mem_Icc, h0, htop]
  -- Icc 版の slice 定義に書き換え
  have : (b - 1) ∈ Finset.filter (fun a => is_bad_a δ X b a) (Finset.Icc 0 X) := by
    simp [Finset.mem_filter, hmem_Icc, hbad]
  -- 1 ≤ カード
  have : (1 : ℕ) ≤ (Finset.filter (fun a => is_bad_a δ X b a) (Finset.Icc 0 X)).card :=
    Finset.one_le_card.mpr ⟨_, this⟩
  -- sliceBadCount に戻す
  simpa [sliceBadCount_eq_card_filter_Icc δ X b]


/-- `diag_badcount_le_badcount` asserts that the diagonal count for parameters `δ` and `X` is less than or equal to the bad count, both interpreted as real numbers. -/
lemma diag_badcount_le_badcount (δ : ℝ) (X : ℕ) :
  (diagCount δ X : ℝ) ≤ BadCount δ X := by
  classical
  -- First, the total sum of sliceBadCount (as reals) is ≤ BadCount (as real)
  have hsum_le : (∑ b ∈ Finset.Icc 0 X, (sliceBadCount (δ:=δ) X b : ℝ))
      ≤ (BadCount δ X : ℝ) := by
    simpa [← range_succ_eq_Icc X] using (by exact_mod_cast slice_sum_le_badcount (δ:=δ) X)

  -- Express diagCount as a sum of indicator naturals and compare pointwise in ℕ
  have eq_nat : diagCount δ X = (∑ b ∈ Finset.Icc 0 X, (if is_bad_a δ X b (b - 1) then (1 : ℕ) else 0)) := by
    simp [diagCount]

  have per_elem_le : ∀ b ∈ Finset.Icc 0 X,
      (if is_bad_a δ X b (b - 1) then (1 : ℕ) else 0) ≤ sliceBadCount (δ:=δ) X b := by
    intro b hb; by_cases h : is_bad_a δ X b (b - 1)
    · have : (1 : ℕ) ≤ sliceBadCount (δ:=δ) X b := one_le_slice_when_diag δ hb h
      simp only [h, ↓reduceIte, ge_iff_le]
      exact this
    · simp only [h, ↓reduceIte, zero_le]

  have le_nat_sum : (∑ b ∈ Finset.Icc 0 X, (if is_bad_a δ X b (b - 1) then (1 : ℕ) else 0))
      ≤ (∑ b ∈ Finset.Icc 0 X, sliceBadCount (δ:=δ) X b) :=
    Finset.sum_le_sum (fun b hb => per_elem_le b hb)

  -- cast the Nat inequality to ℝ and combine with hsum_le
  have : (diagCount δ X : ℝ) ≤ (∑ b ∈ Finset.Icc 0 X, (sliceBadCount (δ:=δ) X b : ℝ)) := by
    rw [eq_nat]
    exact_mod_cast le_nat_sum
  exact this.trans hsum_le


end DkMath.ABC
