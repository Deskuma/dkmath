/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC012

#print "file: DkMath.ABC.ABC013"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-
slice_average_bound: average化 → 大多数のスライスが小さい（Markov 的引数）
ここではまず有限スライス上の簡潔な不等式を Lean 化する。後続で `eventually_badcount_le_eps`
を組み合わせれば `∀ᶠ b, sliceBadCount δ X b ≤ η * X` の形に持ち込める。
-/

/-- η以上のsliceBadCountを持つbの個数は、BadCount δ X / (η * (X + 1)) 以下であることを示す補題 -/
lemma slice_heavy_card_le {δ : ℝ} (η : ℝ) (hη : 0 < η) (X : ℕ) :
  ((Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card ≤
    (BadCount δ X : ℝ) / (η * ((X + 1 : ℕ) : ℝ)) := by
  -- convert counting inequality to numeric bound: each heavy slice contributes at least η*(X+1) to the sum
  let S := (Finset.range (X+1)).filter fun b => ((sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))
  -- each element of S has value ≥ η * (X+1)
  have hge : ∀ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ) := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  -- sum over S ≥ S.card * η * (X+1)
  have hsumS : (∑ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ)) ≥ (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) := by
    have eq : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) = (∑ b ∈ S, η * ((X + 1 : ℕ) : ℝ)) := by
      simp [Finset.sum_const, mul_comm]
    rw [eq]
    apply Finset.sum_le_sum (by intro b hb; exact hge b hb)
  -- extend S-sum to full range using nonnegativity of sliceBadCount
  have hnonneg : ∀ b, 0 ≤ (sliceBadCount (δ := δ) X b : ℝ) := by intro b; exact Nat.cast_nonneg _
  have hfull : (∑ b ∈ S, (sliceBadCount (δ := δ) X b : ℝ)) ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b hb _ => hnonneg b)
  have hsum : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) :=
    le_trans hsumS hfull
  -- now use slice_sum_le_badcount to bound the RHS by BadCount (cast to ℝ)
  have hbad_sum : (∑ b ∈ Finset.range (X+1), (sliceBadCount (δ := δ) X b : ℝ)) ≤ (BadCount δ X : ℝ) :=
    by exact_mod_cast (slice_sum_le_badcount (δ := δ) X)
  have mul_le : (S.card : ℝ) * (η * ((X + 1 : ℕ) : ℝ)) ≤ (BadCount δ X : ℝ) := by linarith [hsum, hbad_sum]
  -- divide by η * (X+1) > 0
  have hXpos : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ X
  have hpos : 0 < η * ((X + 1 : ℕ) : ℝ) := mul_pos hη hXpos
  exact (le_div_iff₀ hpos).mpr mul_le


/-- Eventualization of the slice-average Markov bound.
Given δ and positive η, ε', eventually (for large X) the number of heavy slices
with sliceBadCount ≥ η*(X+1) is at most (ε'/η) * X. This combines the finite
`slice_heavy_card_le` with `eventually_badcount_le_eps` (for δ = 0.435 or general δ
when an appropriate eventually_badcount lemma is available).
-/
theorem eventually_slice_heavy_sublinear
  {δ : ℝ} (hδ_eq : δ = 0.435)
  (η ε' : ℝ) (hη : 0 < η) (hε' : 0 < ε') :
  ∀ᶠ X in atTop,
    ((Finset.range (X+1)).filter
      (fun b => (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card
      ≤ (ε' / η) * (X : ℝ) := by
  -- BadCount ≤ ε' X^2 eventually（既存）
  have hBC := eventually_badcount_le_eps (hδ := hδ_eq) (η := ε') hε'
  -- X≥1 eventually
  have ev1 := (Filter.eventually_atTop.2 ⟨1, by intro k hk; exact hk⟩)
  refine (ev1.and hBC).mono ?_
  intro X ⟨_, hBadLe⟩
  -- 有限版 Markov：|heavy| ≤ BadCount / (η (X+1))
  have h_fin := slice_heavy_card_le (δ:=δ) (η:=η) (hη:=hη) (X:=X)
  -- 右辺を ε' で上から挟む
  have hposX1 : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos X
  have denom_pos : 0 < η * ((X + 1 : ℕ) : ℝ) := mul_pos hη hposX1
  have step1 :
    (BadCount δ X : ℝ) / (η * ((X + 1 : ℕ) : ℝ))
      ≤ (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ)) :=
    (div_le_div_of_nonneg_right hBadLe (le_of_lt denom_pos))
  -- さらに (X^2)/(X+1) ≤ X
  have x2_over_x1_le_x :
    ((X : ℝ)^2) / ((X + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    have hX1pos : 0 < ((X + 1 : ℕ) : ℝ) := hposX1
    -- rewrite (X^2)/(X+1) = X - X/(X+1)
    have hne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
    have eq : ((X : ℝ) ^ 2) / ((X + 1 : ℕ) : ℝ) = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      calc
        ((X : ℝ) ^ 2) / ((X + 1 : ℕ) : ℝ)
          = ((X : ℝ) * ((X + 1 : ℕ) : ℝ) - (X : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
            have rfl_cast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
            rw [rfl_cast]; simp [pow_two, mul_add]
        _ = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by field_simp [hne]
    rw [eq]
    -- X/(X+1) ≥ 0, so X - X/(X+1) ≤ X
    have nonneg_div : 0 ≤ (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le X
      · exact le_of_lt hX1pos
    linarith
  -- まとめ
  have step2 :
    (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ))
      ≤ (ε' / η) * (X : ℝ) := by
    have coef_nonneg : 0 ≤ ε' / η := div_nonneg (le_of_lt hε') (le_of_lt hη)
    have eq : (ε' * (X : ℝ)^2) / (η * ((X + 1 : ℕ) : ℝ))
         = (ε'/η) * (((X : ℝ)^2) / ((X + 1 : ℕ) : ℝ)) := by
      have hη0 : (η:ℝ) ≠ 0 := ne_of_gt hη
      have hX0 : ((X + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hposX1
      field_simp [hη0, hX0, mul_comm, mul_left_comm, mul_assoc]
    rw [eq]
    exact mul_le_mul_of_nonneg_left x2_over_x1_le_x coef_nonneg
  exact (le_trans h_fin (le_trans step1 step2))

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


/-- For any natural number `n`, the real number `rad n` is at least 1. -/
lemma one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp
  · exact_mod_cast abc_one_le_rad hn


/-- The natural logarithm of the radical of `n` is nonnegative. -/
lemma log_rad_nonneg (n : ℕ) : 0 ≤ Real.log (rad n : ℝ) :=
  Real.log_nonneg (one_le_rad_real n)


/-- The logarithm of the product of the radicals of two natural numbers is nonnegative. -/
lemma log_rad_mul_nonneg (a b : ℕ) : 0 ≤ Real.log (rad a * rad b : ℝ) := by
  classical
  have ha : 0 < rad a := by
    by_cases ha0 : a = 0
    · subst ha0
      simp
    · exact rad_pos (Nat.pos_of_ne_zero ha0)
  have hb : 0 < rad b := by
    by_cases hb0 : b = 0
    · subst hb0
      simp
    · exact rad_pos (Nat.pos_of_ne_zero hb0)
  have hprod : 0 < rad a * rad b := Nat.mul_pos ha hb
  have hge : (1 : ℕ) ≤ rad a * rad b := Nat.succ_le_of_lt hprod
  have hge_real : (1 : ℝ) ≤ (rad a * rad b : ℝ) := by exact_mod_cast hge
  exact Real.log_nonneg hge_real


/-- If the total bad count is subquadratic, then for any ε' > 0, the number of slices with bad count at least η times the slice size is sublinear in X. -/
lemma eventually_slice_heavy_sublinear_of_badcount_subquad
  {δ η : ℝ} (hη : 0 < η)
  (hTot : ∀ ε'' > 0, ∀ᶠ X in atTop, (BadCount δ X : ℝ) ≤ ε'' * (X : ℝ) ^ 2) :
  ∀ ε' > 0, ∀ᶠ X in atTop,
  ((Finset.range (X+1)).filter (fun b =>
    (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ))).card
      ≤ (ε' / η) * (X : ℝ) := by
  intro ε' hε'
  -- apply hTot with ε' to bound BadCount by ε' * X^2 eventually
  have hBC := hTot ε' (by linarith)
  have eventual_bound := hBC.mono fun X hbad => by
    have h_fin := slice_heavy_card_le (δ := δ) (η := η) (hη := hη) (X := X)
    -- h_fin : card ≤ BadCount / (η*(X+1)); combine with hbad: BadCount ≤ ε'*X^2
    have hpos_denom : 0 < η * ((X + 1 : ℕ) : ℝ) := by
      have hXpos : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ X
      exact mul_pos hη hXpos
    have h_div := div_le_div_of_nonneg_right hbad (le_of_lt hpos_denom)
    have heavy_le : ((Finset.range (X+1)).filter fun b => (sliceBadCount (δ:=δ) X b : ℝ) ≥ η * ((X + 1 : ℕ) : ℝ)).card
        ≤ (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) := by
      exact le_trans h_fin h_div
    -- since (X : ℝ)^2 / (X+1) ≤ X for X ≥ 0, we get desired bound by algebra
    have hne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
    have eq_div : (X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ) = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      calc
        (X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ) = ((X : ℝ) * ((X + 1 : ℕ) : ℝ) - (X : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
          have rfl_cast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
          rw [rfl_cast]; simp [pow_two, mul_add]
        _ = (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by field_simp [hne]
    have nonneg_div_X : 0 ≤ (X : ℝ) / ((X + 1 : ℕ) : ℝ) := by
      apply div_nonneg
      · exact_mod_cast (Nat.zero_le X)
      · exact le_of_lt (by exact_mod_cast Nat.zero_lt_succ X)
    have frac_le : (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) ≤ (ε' / η) * (X : ℝ) := by
      have hη_ne : η ≠ 0 := ne_of_gt hη
      have hX1_ne : ((X + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero X)
      have eq_field : (ε' * (X : ℝ) ^ 2) / (η * ((X + 1 : ℕ) : ℝ)) = (ε' / η) * ((X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ)) := by
        field_simp [hη_ne, hX1_ne]
      rw [eq_field]
      -- replace (X^2)/(X+1) by X - X/(X+1) and use nonnegativity
      have : (ε' / η) * ((X : ℝ) ^ 2 / ((X + 1 : ℕ) : ℝ)) = (ε' / η) * ((X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ)) := by rw [eq_div]
      rw [this]
      have nonneg_coef : 0 ≤ ε' / η := div_nonneg (le_of_lt hε') (le_of_lt hη)
      have le_sub : (X : ℝ) - (X : ℝ) / ((X + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by linarith [nonneg_div_X]
      exact mul_le_mul_of_nonneg_left le_sub nonneg_coef
    exact le_trans heavy_le frac_le
  exact eventual_bound

end ABC
