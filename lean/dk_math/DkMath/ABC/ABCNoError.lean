/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.Square
import DkMath.ABC.RatioBound

#print "file: DkMath.ABC.ABCNoError"

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

/- 中帯関連の再利用可能補題 -/

variable {δ : ℝ} {X b : ℕ}

-- T 0 has at most one element (only a = 0 can have rad = 0)
/--
Let S be the finset of indices a in range (X+1) satisfying `is_bad_a δ X b a`, and define
`T r := S.filter (fun a => rad a = r)`. This lemma states that the fiber `T 0` has cardinality
at most 1. In other words, among the "bad" indices between 0 and X there is at most one whose
radical equals 0.

Intuitively, `rad a = 0` can only occur for a very restricted value of `a` (in the intended
development this is `a = 0`), so there cannot be two distinct elements of `S` with `rad = 0`.
The proof shows that any two elements of `T 0` must be equal, hence `|T 0| ≤ 1`.

This lemma is useful to rule out the existence of multiple bad indices with radical zero when
performing case splits or counting arguments over `S`.
-/
lemma T_zero_card_le_one :
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let T := fun r => S.filter fun a => rad a = r
  (T 0).card ≤ 1 := by
  dsimp
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let T := fun r => S.filter fun a => rad a = r
  -- T 0 contains at most the element 0, since rad n = 0 iff n = 0
  have hsub : (T 0) ⊆ (Finset.range 1) := by
    intro a ha
    -- a ∈ S.filter (rad a = 0) so rad a = 0 and a ∈ range (X+1)
    rcases Finset.mem_filter.1 ha with ⟨haS, ha_rad_eq⟩
    -- rad a = 0 implies a = 0
    have ha0 : a = 0 := by
      cases a with
      | zero => rfl
      | succ k =>
        -- rad (succ k) > 0, so cannot equal 0
        have hpos := rad_pos (Nat.succ_pos k)
        have h_eq := ha_rad_eq
        linarith
    subst ha0
    -- now a = 0 ∈ range 1
    apply Finset.mem_range.mpr
    simp
  have hcard := Finset.card_le_card hsub
  simp only [Finset.range_one, Finset.card_singleton] at hcard
  exact hcard

-- For r ≠ 0, (T r).card ≤ (X / r) + 1
/-
Bounds the number of "bad" integers in a given radical class.

Given a nonzero natural number `r`, we consider the finite set
`S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a` of
"bad" integers `a` with `0 ≤ a ≤ X`, and the sub-collection
`T r := S.filter fun a => rad a = r` consisting of those `a` whose
radical equals `r`. This lemma asserts that the size of `T r` is
controlled by the trivial bound coming from divisibility:

  (T r).card ≤ (X / r) + 1.

In words: for each fixed radical `r ≠ 0`, there are at most `⌊X/r⌋ + 1`
elements `a ≤ X` with `rad a = r` that are also `is_bad_a δ X b`. The
extra `+1` accounts for the possible element `0` or an off-by-one from
integer division conventions.

Parameters:
- `r` : the radical value to fix (assumed nonzero).
- `hr` : proof that `r ≠ 0`.

Remarks:
- `Finset.range (X+1)` enumerates the integers `0,1,...,X`.
- `rad a` denotes the radical of `a` (product of distinct prime factors).
- The lemma is typically used to sum or bound contributions from each
  radical class by reducing to a simple divisor-counting estimate.
- The proof proceeds by observing that every `a` with `rad a = r` is
  of the form `r * m` with `m ≤ X / r`, yielding the stated bound.
-/
lemma Tr_card_le_div_plus_one (r : ℕ) (hr : r ≠ 0) :
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let T := fun r => S.filter fun a => rad a = r
  (T r).card ≤ (X / r) + 1 := by
  dsimp
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let T := fun r => S.filter fun a => rad a = r
  -- show T r ⊆ (range (X+1)).filter (λ a, a ≤ X ∧ rad a = r)
  have hsub : (T r) ⊆ (Finset.range (X+1)).filter fun a => a ≤ X ∧ rad a = r := by
    intro a ha
    rcases Finset.mem_filter.1 ha with ⟨haS, ha_rad_eq⟩
    rcases Finset.mem_filter.1 haS with ⟨ha_range, _⟩
    have a_le := Nat.le_of_lt_succ (Finset.mem_range.mp ha_range)
    exact Finset.mem_filter.2 ⟨ha_range, ⟨a_le, ha_rad_eq⟩⟩
  have hcard_le := Finset.card_le_card hsub
  have hcount := count_with_rad_eq_le_div r X hr
  calc
    (T r).card ≤ ((Finset.range (X+1)).filter fun a => a ≤ X ∧ rad a = r).card := hcard_le
    _ ≤ (X / r) + 1 := hcount

-- Partition S by rad: S.card = sum_{r ∈ range (X+1)} (T r).card
/--
Partition S by the value of `rad` and express its cardinality as the sum of the sizes
of the fibres.

Let
  * `S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a` be the finite set of
    indices `a ∈ {0, …, X}` satisfying the predicate `is_bad_a δ X b a`,
  * `s := Finset.range (X+1)` be the index range,
  * `T := fun r => S.filter fun a => rad a = r` be the family of subsets of `S`
    consisting of those `a` with given radical `r`.

The lemma states that the sets `T r` partition `S` (they are pairwise disjoint and their
union is `S`), hence the cardinality of `S` equals the sum over `r ∈ s` of the
cardinalities `(T r).card`. The summands for values of `r` not occurring as `rad a`
are zero, so the sum is finite and well-defined.

Proof sketch: show that every `a ∈ S` belongs to exactly one `T r` (with `r = rad a`),
so `S = ⋃ r, T r` and the `T r` are disjoint; then use basic Finset cardinality
properties to turn the partition into a sum of cardinalities.
-/
lemma slice_partition_by_rad :
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let s := Finset.range (X+1)
  let T := fun r => S.filter fun a => rad a = r
  S.card = s.sum fun r => (T r).card := by
  dsimp
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let s := Finset.range (X+1)
  let T := fun r => S.filter fun a => rad a = r
  let f : ℕ → Σ r : ℕ, ℕ := fun a => Sigma.mk (rad a) a
  let img := S.image f
  -- show img = Finset.sigma s T
  have img_eq_sigma : img = Finset.sigma s T := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.1 hy with ⟨a, haS, rfl⟩
      rcases Finset.mem_filter.1 haS with ⟨ha_range, ha_bad⟩
      -- we show rad a ∈ s (i.e. rad a ≤ X) for any a ∈ S.
      let r := rad a
      have a_le : a ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp ha_range)
      have hr_mem : r ∈ s := by
        -- two cases: a = 0 or a ≠ 0. If a ≠ 0 then rad_le gives rad a ≤ a ≤ X.
        by_cases ha0 : a = 0
        · -- a = 0. From is_bad_a we get a Coprime witness; substitute a = 0 first.
          subst ha0
          rcases ha_bad with ⟨hcop, rest⟩
          -- hcop : Coprime 0 b, so Nat.coprime_iff_gcd_eq_one gives gcd 0 b = 1, and gcd 0 b = b
          have hb1 : b = 1 := by
            have hg := Nat.coprime_iff_gcd_eq_one.mp hcop
            have g0 : Nat.gcd 0 b = b := by simp [Nat.gcd_zero_left]
            rw [g0] at hg
            exact hg
          -- use b ≤ X from the rest witness to deduce X ≥ 1
          rcases rest with ⟨_a_le, hb_le, _hab_le, _bad⟩
          have : 1 ≤ X := by
            subst hb1
            exact hb_le
          -- rad 0 = 1, so r = 1; thus r < X+1
          have hr0val : r = 1 := by dsimp [r]; simp [ABC.rad_zero]
          rw [hr0val]
          apply Finset.mem_range.mpr
          exact Nat.lt_succ_of_le this
        · -- a ≠ 0, use rad_le
          have hrad_le := rad_le ha0
          apply Finset.mem_range.mpr
          exact Nat.lt_succ_of_le (Nat.le_trans hrad_le a_le)
      have ha_in_Tr : a ∈ T r := Finset.mem_filter.2 ⟨haS, rfl⟩
      exact Finset.mem_sigma.2 ⟨hr_mem, ha_in_Tr⟩
    · intro hy
      let hsig := Finset.mem_sigma.1 hy
      have ha_in_Tr := hsig.2
      -- a ∈ T r implies a ∈ S; use projections to avoid dependent-elimination
      let p := Finset.mem_filter.1 ha_in_Tr
      let haS := p.1
      let ha_rad_eq := p.2
      have : f (y.snd) = y := by
        dsimp [f]
        cases y with
        | mk r' a' =>
          dsimp at ha_rad_eq
          -- after destructuring, ha_rad_eq states rad a' = r', so the two Sigmas are definitionally equal
          simp [ha_rad_eq]
      exact Finset.mem_image.2 ⟨y.snd, haS, this⟩
  -- f is injective, so img.card = S.card
  have finj : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    injection h with _ h2
  have img_card_eq_S : img.card = S.card := by dsimp [img]; exact Finset.card_image_of_injective S finj
  -- conclude using card_sigma
  calc
    S.card = img.card := by rw [← img_card_eq_S]
    _ = (Finset.sigma s T).card := by rw [← img_eq_sigma]
    _ = s.sum fun r => (T r).card := by simp [Finset.card_sigma]

-- Final bound: sliceBadCount ≤ sum_r (if r=0 then 1 else (X/r)+1)
/--
An upper bound on `sliceBadCount δ X b` by a simple sum over divisor-like indices.

More precisely, for the given parameters `δ`, `X` and `b`, the number of "bad"
slices counted by `sliceBadCount δ X b` is at most the sum
`(Finset.range (X+1)).sum fun r => if r = 0 then 1 else (X / r) + 1`.
The summand for `r = 0` is treated as a special case (`1`), while each
nonzero `r` contributes at most `(X / r) + 1` to the total.

Intuition / proof idea:
- Partition the bad slices into classes indexed by an auxiliary integer `r`
  (roughly a step-size or modulus parameter).
- Show that for each nonzero `r` there are at most `X / r + 1` slices in that
  class, and at most `1` slice when `r = 0`.
- Summing these bounds over `r = 0, 1, ..., X` yields the claimed inequality.

This lemma provides a crude but useful complexity bound on `sliceBadCount`
that is often sufficient for subsequent estimates.
-/
lemma sliceBadCount_le_sum_div_plus_one :
  sliceBadCount δ X b ≤ (Finset.range (X+1)).sum fun r => if r = 0 then 1 else (X / r) + 1 := by
  dsimp [sliceBadCount]
  let S := (Finset.range (X+1)).filter fun a => is_bad_a δ X b a
  let s := Finset.range (X+1)
  let T := fun r => S.filter fun a => rad a = r
  -- partition S into fibers T r (instantiate lemma with local S,s,T to avoid implicit-arg issues)
  have hpart : S.card = s.sum fun r => (T r).card := by
    dsimp [S, s, T]
    exact slice_partition_by_rad
  -- pointwise bound for each r in s
  have hpointwise : ∀ r ∈ s, (T r).card ≤ if r = 0 then 1 else (X / r) + 1 := by
    intro r hr
    by_cases hr0 : r = 0
    · -- r = 0
      simp only [hr0, ↓reduceIte]
      -- use T 0 bound (inline to avoid implicit-arg synthesis problems)
      have hsub : (T 0) ⊆ (Finset.range 1) := by
        intro a ha
        rcases Finset.mem_filter.1 ha with ⟨haS, ha_rad_eq⟩
        -- rad a = 0 implies a = 0
        have ha0 : a = 0 := by
          cases a with
          | zero => rfl
          | succ k =>
            have hpos := rad_pos (Nat.succ_pos k)
            have h_eq := ha_rad_eq
            linarith
        subst ha0
        apply Finset.mem_range.mpr
        simp
      have hcard := Finset.card_le_card hsub
      simp only [Finset.range_one, Finset.card_singleton] at hcard
      exact hcard
    · -- r ≠ 0 case: inline the Tr_card_le_div_plus_one proof to avoid implicit arg inference
      have hsub : (T r) ⊆ (Finset.range (X+1)).filter fun a => a ≤ X ∧ rad a = r := by
        intro a ha
        rcases Finset.mem_filter.1 ha with ⟨haS, ha_rad_eq⟩
        rcases Finset.mem_filter.1 haS with ⟨ha_range, _⟩
        have a_le := Nat.le_of_lt_succ (Finset.mem_range.mp ha_range)
        exact Finset.mem_filter.2 ⟨ha_range, ⟨a_le, ha_rad_eq⟩⟩
      have hcard_le := Finset.card_le_card hsub
      have hcount := count_with_rad_eq_le_div r X hr0
      have hfinal : (T r).card ≤ if r = 0 then 1 else X / r + 1 := by
        simpa [hr0] using le_trans hcard_le hcount
      exact hfinal
  -- sum the pointwise bounds over s and use equality from partition
  have hsum_le := Finset.sum_le_sum (by intro r hr; exact hpointwise r hr)
  calc
    sliceBadCount δ X b = S.card := by rfl
    _ = s.sum fun r => (T r).card := by exact hpart
    _ ≤ s.sum fun r => if r = 0 then 1 else (X / r) + 1 := by exact hsum_le

-- ### 補助：`(C+1)/X^α → 0` （α>0）

/--
`α` > 0 なら K / X^α → 0 （X → ∞）

`α` を正の実数、`K` を実数とするとき、関数 `X ↦ K / X^α`（`X` は自然数）は、`X` が無限大に近づくとき 0 に収束することを示す補題です。
この補題は、数列の極限に関する基本的な性質を利用しています。
- `hα : 0 < α` は、分母のべき乗が十分に速く増加するために必要な仮定です。
-/
lemma tendsto_const_div_nat_rpow_atTop_0 {α K : ℝ}
  (hα : 0 < α) :
  Tendsto (fun X : ℕ => K / (X : ℝ) ^ α) atTop (nhds 0) := by
  -- K = 0 の場合は自明
  by_cases hK0 : K = 0
  · simp [hK0]
  -- 以降 K ≠ 0, 任意の ε>0 に対して N を取って |K|/X^α < ε を示す
  intro U heps
  -- 近傍 U ∈ nhds 0 から正の実数 ε を取り出す
  obtain ⟨eps, heps_pos, heps_mem⟩ := Metric.mem_nhds_iff.1 heps
  -- 定義 M = ((|K|)/eps)^(1/α) とし、N := ⌈M⌉₊ + 1 を取る（これで N > M となる）
  let M : ℝ := (abs K / eps) ^ (1 / α)
  let N := (⌈M⌉₊ : ℕ) + 1
  -- 証明すべきは Set.Ici N ∈ map (fun X ↦ K / ↑X ^ α) atTop
  apply Filter.mem_map.2
  apply Filter.eventually_atTop.2
  use N
  intro X hXge
  -- X ≥ N なら |K / X^α| < eps を補題で示し、U の近傍に入れる
  have hK_ne' : K ≠ 0 := by simpa using hK0
  have hsmall : |K / (X : ℝ) ^ α| < eps :=
    abs_div_lt_for_large_nat α K eps hα heps_pos hK_ne' X hXge
  have h_in_ball : K / (X : ℝ) ^ α ∈ Metric.ball 0 eps := by
    simp only [gt_iff_lt, ge_iff_le, ne_eq, abs_div, Metric.mem_ball, dist_zero_right, norm_div,
      norm_eq_abs] at *
    exact hsmall
  exact heps_mem h_in_ball

/-- 固定 X に対し「多すぎるスライス」を抜き出す集合：
    `heavySlice s η X = { b≤X | (s b X) ≥ η·X }` -/
noncomputable def heavySlice (s : ℕ → ℕ → ℕ) (η : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X+1)).filter (fun b => (η * (X : ℝ) ≤ (s b X : ℝ)))

/-- 基本不等式：
    ∑_b s(b,X) が上から抑えられ、各 heavy b で s(b,X) ≥ η·X なら
    heavy の個数は `≤ (∑ s(b,X)) / (η·X)` に抑え込める（X≥1, η>0）。 -/
lemma heavy_card_le_of_sum_bound
  (s : ℕ → ℕ → ℕ) (η : ℝ) (X : ℕ)
  (hη : 0 < η) (hX : 1 ≤ X)
  (hsum_ub : (∑ b ∈ Finset.range (X + 1), (s b X : ℝ)) ≤ (BadCount 0.435 X : ℝ)) :
  ((heavySlice s η X).card : ℝ)
    ≤ (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹) := by
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hdenpos : 0 < η * (X : ℝ) := mul_pos hη hXpos
  -- heavy 上では点ごとに η·X ≤ s(b,X)
  have hpoint : ∀ {b}, b ∈ heavySlice s η X → (η * (X : ℝ)) ≤ (s b X : ℝ) := by
    intro b hb
    rcases Finset.mem_filter.1 hb with ⟨hbR, hbP⟩
    simpa using hbP
  -- ∑_{b∈heavy} η·X ≤ ∑_{b∈heavy} s(b,X) ≤ ∑_{b≤X} s(b,X)
  have hsum_const_le : (∑ _b ∈ heavySlice s η X, (η * (X : ℝ)))
      ≤ (∑ b ∈ heavySlice s η X, (s b X : ℝ)) :=
    Finset.sum_le_sum (by intro b hb; exact hpoint hb)

  have hsum_heavy_le_all :
      (∑ b ∈ heavySlice s η X, (s b X : ℝ))
      ≤ (∑ b ∈ Finset.range (X+1), (s b X : ℝ)) := by
    -- express the sum over the filtered set as a sum over the full range with an ite
    have hsum_eq : (∑ b ∈ heavySlice s η X, (s b X : ℝ))
        = (∑ b ∈ Finset.range (X+1), ite (η * (X : ℝ) ≤ (s b X : ℝ)) (s b X : ℝ) 0) := by
      -- heavySlice s η X is definitionally (Finset.range (X+1)).filter _
      dsimp [heavySlice]
      rw [Finset.sum_filter]
    -- pointwise bound: for b ∈ range, ite (η*X ≤ s b X) _ ≤ s b X because s b X ≥ 0
    have hpoint_le : ∀ b ∈ Finset.range (X+1), ite (η * (X : ℝ) ≤ (s b X : ℝ)) (s b X : ℝ) 0 ≤ (s b X : ℝ) := by
      intro b hb
      by_cases h : (η * (X : ℝ) ≤ (s b X : ℝ))
      · simp [h]
      · simp [h]
    calc
      (∑ b ∈ heavySlice s η X, (s b X : ℝ)) = (∑ b ∈ Finset.range (X+1), ite (η * (X : ℝ) ≤ (s b X : ℝ)) (s b X : ℝ) 0) := hsum_eq
      _ ≤ (∑ b ∈ Finset.range (X+1), (s b X : ℝ)) := Finset.sum_le_sum hpoint_le
  have hconst_sum :
      (∑ _b ∈ heavySlice s η X, (η * (X : ℝ)))
        = (η * (X : ℝ)) * (heavySlice s η X).card := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [mul_comm]
  -- まとめて割る
  have h_mul_le : (η * (X : ℝ)) * (heavySlice s η X).card
        ≤ (BadCount 0.435 X : ℝ) := by
    have := le_trans hsum_const_le hsum_heavy_le_all
    have := le_trans this hsum_ub
    simpa [hconst_sum, mul_comm] using this
  -- (η*X) > 0 のもとで両辺にその逆数を掛けて整理する
  have ht_nonzero : (η * (X : ℝ)) ≠ 0 := ne_of_gt hdenpos
  have hrecip_pos : 0 < (1 / (η * (X : ℝ))) := div_pos (by norm_num : (0 : ℝ) < 1) hdenpos
  calc
    (heavySlice s η X).card
        = (1 / (η * (X : ℝ))) * ((η * (X : ℝ)) * (heavySlice s η X).card) := by field_simp [ht_nonzero]
    _ ≤ (1 / (η * (X : ℝ))) * (BadCount 0.435 X : ℝ) := mul_le_mul_of_nonneg_left h_mul_le (le_of_lt hrecip_pos)
    _ = (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹) := by field_simp [hdenpos]

/-- **マルコフ不等式（離散版） with BadCount**：
    `∑_b s(b,X) ≤ BadCount(X)` を仮定すると，
    heavy スライスの個数は `≤ BadCount(X)/(η·X)`。 -/
lemma heavy_card_le_of_sum_le_badcount
  (s : ℕ → ℕ → ℕ) (η : ℝ) (X : ℕ)
  (hη : 0 < η) (hX : 1 ≤ X)
  (hsum_le : (∑ b ∈ Finset.range (X + 1), (s b X : ℝ)) ≤ (BadCount 0.435 X : ℝ)) :
  ((heavySlice s η X).card : ℝ)
    ≤ (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹) :=
  heavy_card_le_of_sum_bound s η X hη hX hsum_le

/-- **密度1への転送**：
    加えて `BadCount/X^2 → 0` があると，任意 ε'>0 で十分大の X 以降，
    heavy スライスは高々 (ε'/η)·X 個。 -/
theorem eventually_heavy_sublinear
  (s : ℕ → ℕ → ℕ)
  (hsum_le :
    ∀ᶠ X in atTop, (∑ b ∈ Finset.range (X + 1), (s b X : ℝ)) ≤ (BadCount 0.435 X : ℝ))
  (η ε' : ℝ) (hη : 0 < η) (hε' : 0 < ε') :
  ∀ᶠ X in atTop,
    ((heavySlice s η X).card : ℝ) ≤ (ε' / η) * (X : ℝ) := by
  -- BadCount ≤ ε'·X^2 を eventually 得る
  have hBC := eventually_badcount_le_eps (hδ := rfl) (η := ε') hε'
  -- X≥1 を同時に課す（分母正の保証）
  let ev1 := Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩
  -- 3つを合流
  have hall := hsum_le.and (hBC.and ev1)
  refine hall.mono ?_
  intro X ⟨hsum, ⟨hBad, hXge1⟩⟩
  -- heavy ≤ BadCount/(η·X) ≤ (ε'·X^2)/(η·X) = (ε'/η)·X
  have h1 :
      ((heavySlice s η X).card : ℝ)
        ≤ (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹) :=
    heavy_card_le_of_sum_le_badcount s η X hη hXge1 hsum
  have hXpos : 0 < (X : ℝ) := by
    have : (0 : ℕ) < 1 := by norm_num
    exact_mod_cast lt_of_lt_of_le this hXge1
  have h2 :
    (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹)
      ≤ (ε' * (X : ℝ) ^ 2) * ((X : ℝ)⁻¹ * η⁻¹) := by
    -- multiply both sides of hBad by the nonnegative factor (X⁻¹ * η⁻¹)
    have hdenpos : 0 < η * (X : ℝ) := mul_pos hη hXpos
    have hrecip_pos : 0 < (1 / (η * (X : ℝ))) := div_pos (by norm_num : (0 : ℝ) < 1) hdenpos
    calc
      (BadCount 0.435 X : ℝ) * ((X : ℝ)⁻¹ * η⁻¹) = (1 / (η * (X : ℝ))) * (BadCount 0.435 X : ℝ) := by
        field_simp [hdenpos]
      _ ≤ (1 / (η * (X : ℝ))) * (ε' * (X : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hBad (le_of_lt hrecip_pos)
      _ = (ε' * (X : ℝ) ^ 2) * ((X : ℝ)⁻¹ * η⁻¹) := by field_simp [hdenpos]
  -- 右辺を整理： (ε'·X^2)/(η·X) = (ε'/η)·X
  have h3 : (ε' * (X : ℝ) ^ 2) * ((X : ℝ)⁻¹ * η⁻¹) = (ε' / η) * (X : ℝ) := by
    have hxpos : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    field_simp [hxpos, hη.ne']
  have final := le_trans h1 h2
  -- rewrite RHS of final using h3 to get (ε'/η) * X
  change ↑(heavySlice s η X).card ≤ ε' / η * ↑X
  rw [h3] at final
  exact final

/-- If a predicate holds for all x, it eventually holds at the top (for directed, nonempty α). -/
def eventually_of_forall {α : Type*} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] {p : α → Prop} :
  (∀ x, p x) → ∀ᶠ x in (atTop : Filter α), p x :=
  fun h => eventually_atTop.2 ⟨Nonempty.some (inferInstance : Nonempty α), fun x _ => h x⟩

/- Helper predicate that packages the pair-wise predicate used in counting -/
def BadPair (δ : ℝ) (X : ℕ) (p : ℕ × ℕ) : Prop :=
  let a := p.1; let b := p.2; let c := a + b
  a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
    let lhs := (c.factorization.support.filter fun q => 2 ≤ c.factorization q).prod id
    let rhs := (rad a * rad b : ℕ)
    (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)


/-- 「ほとんどの b は軽い」：heavy スライスは (ε'/η)·X 本以下（X → ∞ で成立）
    Here we fix the δ parameter to 0.435 to match the expectations of eventually_heavy_sublinear. -/
theorem eventually_most_slices_light
  (η ε' : ℝ) (hη : 0 < η) (hε' : 0 < ε') :
  ∀ᶠ X in atTop,
    ((heavySlice (fun b X => sliceBadCount 0.435 X b) η X).card : ℝ) ≤ (ε' / η) * (X : ℝ) := by
  -- use the same fixed δ = 0.435 for the facts below
  let sliceBadCount_swapped := fun b X => sliceBadCount 0.435 X b

  have hsum_le : ∀ᶠ X in atTop,
      (∑ b ∈ Finset.range (X+1), (sliceBadCount_swapped b X : ℝ)) ≤ (BadCount 0.435 X : ℝ) :=
    eventually_of_forall fun X => by
      have := slice_sum_le_badcount 0.435 X
      exact_mod_cast this

  -- swapped 関数を渡す
  exact eventually_heavy_sublinear
    sliceBadCount_swapped (hsum_le := hsum_le)
    (η := η) (ε' := ε') hη hε'

/- Bad は差クラス mod M に平均 ±小誤差で散る（弱均一性） -/
/- NOTE: Axiomatic assumption (placeholder).
   `Bad_diff_uniform` asserts a weak uniform distribution of bad pairs
   across residue classes modulo M. This is a probabilistic / equidistribution
   style input that the formalisation currently takes as an assumption.
   Replace with a proved lemma (or explicitly provide a proof sketch
   using combinatorial/probabilistic techniques) when available.
  -/
axiom Bad_diff_uniform
  (δ : ℝ) :
  ∀ ε' > 0, ∀ᶠ X in atTop,
    ∀ (M : ℕ), 1 ≤ M ∧ M ≤ X →
    ∀ (t : ℤ),
      ((@Finset.filter (ℕ × ℕ)
          (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % M = t ∧ BadPair δ X p)
          (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % M = t ∧ BadPair δ X p))
          ((Finset.range (X+1)).product (Finset.range (X+1)))).card : ℝ)
      ≤ (BadCount δ X : ℝ) / M + ε' * X

/-- 対角一本の Bad 本数は o(X) （解析入力） -/
/- NOTE: Axiomatic assumption (placeholder).
   `Bad_diagonal_sublinear` states a diagonal sublinear bound for the bad
   diagonal slices. It can often be proven from `Bad_diff_uniform` and
   density bounds; here it is left as an axiom for modularity. Plan to
   replace it with a proved lemma once the required probabilistic inputs
   or counting lemmas are implemented.
  -/
axiom Bad_diagonal_sublinear
  (δ : ℝ) :
  ∀ ε' > 0, ∀ᶠ X in atTop,
    ((Finset.filter (fun b => b ≤ X ∧ is_bad_a δ X b (b-1)) (Finset.Icc 0 X)).card : ℝ) ≤ X^(3/4 + ε')

/-- 対角 bad の本数：b=1..X で a=b-1 が bad な b の個数 -/
noncomputable def diagBadCount (δ : ℝ) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun b =>
    is_bad_a δ X b (b-1))).card

theorem diagBadCount_le_BadCount (δ : ℝ) (X : ℕ) :
  diagBadCount δ X ≤ BadCount δ X := by
  -- diagBadCount counts b ∈ [1..X] with is_bad_a δ X b (b-1).
  dsimp [diagBadCount]
  let S := (Finset.Icc 1 X).filter (fun b => is_bad_a δ X b (b-1))

  -- build the same ranges and predicate P as in BadCount
  let ranges := ((Finset.range (X+1)).product (Finset.range (X+1))).product (Finset.range (X+1))
  let P := fun t : (ℕ × ℕ) × ℕ =>
    let a := t.1.1; let b := t.1.2; let c := t.2
    a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
      let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id
      let rhs := (rad a * rad b : ℕ)
      (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)

  let f := fun b : ℕ => ((b - 1, b), (b - 1) + b)
  let img := S.image f

  -- show img ⊆ ranges.filter P
  have img_sub : img ⊆ ranges.filter P := by
    intro y hy
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.1 hy
    rcases Finset.mem_filter.1 hbS with ⟨hb_range, hbP⟩
    -- hbP : is_bad_a δ X b (b-1)
    rcases hbP with ⟨hcop, rest⟩
    rcases rest with ⟨h1, rest₂⟩
    rcases rest₂ with ⟨h2, rest₃⟩
    rcases rest₃ with ⟨h3, hbad⟩
    -- membership in ranges
    have haR : (b - 1) ∈ Finset.range (X+1) := by
      apply Finset.mem_range.mpr; exact Nat.lt_succ_of_le h1
    have hbR' : b ∈ Finset.range (X+1) := by
      apply Finset.mem_range.mpr; exact Nat.lt_succ_of_le h2
    have hpair : (b - 1, b) ∈ (Finset.range (X+1)).product (Finset.range (X+1)) :=
      Finset.mem_product.2 ⟨haR, hbR'⟩
    have hsum : (b - 1) + b ∈ Finset.range (X+1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le h3)
    have hin_ranges : f b ∈ ranges := Finset.mem_product.2 ⟨hpair, hsum⟩
    -- predicate P holds for f b
    have hP : P (f b) := by dsimp [P, f]; exact ⟨h1, h2, h3, rfl, hcop, hbad⟩
    exact Finset.mem_filter.2 ⟨hin_ranges, hP⟩

  -- image is injective so img.card = S.card
  have finj : Function.Injective f := fun x y h => congrArg (fun t => t.1.2) h

  -- build B (BadCount's concrete filter) with same Decidable witness
  let B := (@Finset.filter ((ℕ × ℕ) × ℕ)
    (fun t =>
      let a := t.1.1; let b := t.1.2; let c := t.2;
      a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
        let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id;
        let rhs := (rad a * rad b : ℕ);
        (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ))
    (fun t => Classical.propDecidable (P t)) ranges)

  have B_eq_ranges_filter : B = ranges.filter P := by
    ext t
    dsimp [B, P]
    simp

  have img_sub_B : img ⊆ B := by
    intro y hy
    have hyR := img_sub hy
    rwa [← B_eq_ranges_filter] at hyR

  have img_card_le_B : img.card ≤ B.card := Finset.card_le_card img_sub_B
  have img_eq_S : img.card = S.card := by dsimp [img]; exact Finset.card_image_of_injective S finj
  have S_card_le_B : S.card ≤ B.card := by rw [← img_eq_S]; exact img_card_le_B

  -- relate S.card to diagBadCount and B.card to BadCount
  have hS_eq : S.card = diagBadCount δ X := rfl
  have hB_eq : B.card = BadCount δ X := rfl
  calc
    diagBadCount δ X = S.card := (Eq.symm hS_eq)
    _ ≤ B.card := S_card_le_B
    _ = BadCount δ X := hB_eq

/- Adjacent 族：ほぼ全 n で q ≤ 1+ε -/

/-- 質の正規定義：q = log c / log rad(abc)（実数にキャスト） -/
noncomputable def quality (T : Triple) : ℝ :=
  Real.log (T.c) / Real.log (rad (T.a * T.b * T.c))

/-- Helper: if b ∈ (Icc 1 X).filter is_bad_a then (b-1,b) belongs to the residue=1 ∧ BadPair filter. -/
theorem mem_image_g_mem_residue {X : ℕ} {b : ℕ}
  (hbS : b ∈ (Finset.Icc 1 X).filter (fun b => is_bad_a 0.435 X b (b - 1)))
  (hXge2 : X ≥ 2) :
  (b - 1, b) ∈ (@Finset.filter (ℕ × ℕ)
    (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % (X : ℤ) = (1 : ℤ) ∧ BadPair 0.435 X p)
    (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % (X : ℤ) = (1 : ℤ) ∧ BadPair 0.435 X p))
    ((Finset.range (X+1)).product (Finset.range (X+1)))) := by
  rcases Finset.mem_filter.1 hbS with ⟨hbIcc, hbBad⟩
  rcases Finset.mem_Icc.1 hbIcc with ⟨hb1, hbX⟩
  rcases hbBad with ⟨hcop, hrest⟩
  rcases hrest with ⟨ha_le, hrest2⟩
  rcases hrest2 with ⟨hb_le, hrest3⟩
  rcases hrest3 with ⟨hab_le, hBadCond⟩
  have haR : b-1 ∈ Finset.range (X+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le ha_le)
  have hbR : b ∈ Finset.range (X+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb_le)
  have hPair : (b-1, b) ∈ (Finset.range (X+1)).product (Finset.range (X+1)) := Finset.mem_product.2 ⟨haR, hbR⟩
  -- removed duplicate direct difference proof; use projections below

  have one_lt_X : (1 : ℤ) < (X : ℤ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hXge2
  -- express the nat difference and show it equals 1 using pred/succ decomposition
  have hnat : b - (b - 1) = 1 := by
    have hb_pos : 0 < b := by linarith [hb1]
    have hb_eq : b = Nat.pred b + 1 := by rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hb_pos]
    rw [hb_eq]
    simp only [add_tsub_cancel_right, add_tsub_cancel_left]

  have hResid1 : (((b - 1, b).2 : ℤ) - ((b - 1, b).1 : ℤ)) % (X : ℤ) = (1 : ℤ) := by
    -- rewrite the integer difference using Int.ofNat_sub (since b-1 ≤ b)
    have hdiff : ((b - 1, b).2 : ℤ) - ((b - 1, b).1 : ℤ) = (b - (b - 1) : ℕ) := by
      have hle : b - 1 ≤ b := Nat.sub_le _ _
      -- projections simplify to b and b - 1
      simp
    -- the natural difference is 1 (already obtained as hnat)
    have hdiff' : ((b - 1, b).2 : ℤ) - ((b - 1, b).1 : ℤ) = 1 := by simpa [hnat] using hdiff
    -- conclude the modulus is 1 since 0 ≤ 1 < X
    simpa [hdiff'] using Int.emod_eq_of_lt (by norm_num : 0 ≤ (1 : ℤ)) one_lt_X
  have hBP : BadPair 0.435 X (b-1, b) := by dsimp [BadPair]; exact ⟨ha_le, hb_le, hab_le, rfl, hcop, hBadCond⟩
  let dec : DecidablePred (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % (X : ℤ) = (1 : ℤ) ∧ BadPair 0.435 X p) :=
    fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % (X : ℤ) = (1 : ℤ) ∧ BadPair 0.435 X p)
  let R := @Finset.filter (ℕ × ℕ)
    (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % (X : ℤ) = (1 : ℤ) ∧ BadPair 0.435 X p)
    dec
    ((Finset.range (X+1)).product (Finset.range (X+1)))
  have memR : (b - 1, b) ∈ R := Finset.mem_filter.2 ⟨hPair, ⟨hResid1, hBP⟩⟩
  exact memR

/-- 近接品質の橋 -/
/- NOTE: Axiomatic assumption (placeholder).
   `adjacent_quality_le_ae` packages an analytic bridge from diagonal
   control to almost-everywhere quality bounds for the Adjacent family.
   Currently left as an `axiom` to keep the dependence explicit. Replace
   with a constructive proof (using `Bad_diagonal_sublinear` or
   combinatorial lemmas) when available.
  -/
axiom adjacent_quality_le_ae (ε : ℝ) (hε : 0 < ε)
  (hDiag : ∀ ε' > 0, ∀ᶠ X in atTop, ((Finset.filter (fun b => b ≤ X ∧ is_bad_a 0.435 X b (b - 1)) (Finset.Icc 0 X)).card : ℝ) ≤ X ^ (3 / 4 + ε')) :
  ∀ᶠ n in atTop, quality (Triple.mk n (n+1) (2*n+1) (by ring : n + (n + 1) = 2 * n + 1) (coprime_succ n)) ≤ 1 + ε

/- k-parameterised diagonal control and analytic bridge -/
/- NOTE: these are the k-general versions of the adjacent axioms used for AdjK. -/
axiom Bad_diagonal_sublinear_k
  (δ : ℝ) (k : ℕ) :
  ∀ ε' > 0, ∀ᶠ X in atTop,
    ((Finset.filter (fun b => b ≤ X ∧ is_bad_a δ X b (b - k)) (Finset.Icc 0 X)).card : ℝ) ≤ X^(3/4 + ε')

/- analytic bridge for AdjK family -/
axiom adjacent_quality_le_ae_k (k : ℕ) (ε : ℝ) (hε : 0 < ε)
  (hDiag : ∀ ε' > 0, ∀ᶠ X in atTop, ((Finset.filter (fun b => b ≤ X ∧ is_bad_a 0.435 X b (b - k)) (Finset.Icc 0 X)).card : ℝ) ≤ X ^ (3 / 4 + ε')) :
  -- quantify over an arbitrary coprimality witness so this axiom can be instantiated
  -- with any specific Triple (e.g. `AdjK k n`) by providing its `hcop` field.
  ∀ᶠ n in atTop, ∀ (hcop : Nat.Coprime n (n + k)),
    quality (Triple.mk n (n + k) (2 * n + k) (by ring : n + (n + k) = 2 * n + k) hcop) ≤ 1 + ε

/-- Keystone-style eventual implication for AdjK (uses the k-axiom above) -/
theorem Keystone_bridge_quality_adjacent_imp_k (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ n in atTop, ∀ (hcop : Nat.Coprime n (n + k)),
    (¬ Bad 0.435 (Triple.mk n (n + k) (2 * n + k) (by ring : n + (n + k) = 2 * n + k) hcop) →
      quality (Triple.mk n (n + k) (2 * n + k) (by ring : n + (n + k) = 2 * n + k) hcop) ≤ 1 + ε) := by
  have hDiag := Bad_diagonal_sublinear_k 0.435 k
  have h_adjk_ae := adjacent_quality_le_ae_k k ε hε hDiag
  -- h_adjk_ae : ∀ᶠ n, ∀ hcop, quality (...) ≤ 1+ε, so it implies (¬Bad → quality ≤ 1+ε) pointwise
  exact h_adjk_ae.mono (fun n h_all => fun hcop => fun _ => h_all hcop)

-- --------------------------------------------------------------------------------------------------------------------

/-- 対角 bad の本数は o(X)：`Bad_diff_uniform` と `BadCount/X^2 → 0` から。
    すなわち任意 ε>0 に対して最終的に `diagBadCount ≤ ε·X`. -/
theorem eventually_diagBadCount_oX
  (hU : ∀ ε' > 0, ∀ᶠ X in atTop,
      ∀ (M : ℕ), 1 ≤ M ∧ M ≤ X →
      ∀ (t : ℤ),
        ((@Finset.filter (ℕ × ℕ)
            (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % M = t ∧ BadPair 0.435 X p)
            (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % M = t ∧ BadPair 0.435 X p))
            ((Finset.range (X + 1)).product (Finset.range (X + 1)))).card : ℝ)
        ≤ (BadCount 0.435 X : ℝ) / M + ε' * X)
  (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ X in atTop, (diagBadCount 0.435 X : ℝ) ≤ ε * (X : ℝ) := by
  -- 均一性の小項（ε/2）と BadCount の小項（ε/2）を用意
  have hε2 : 0 < ε/2 := by linarith
  -- 均一性：最終的に ∀ M∈[1,X], ∀t,  residue-count ≤ BadCount/M + (ε/2)·X
  have hU' := hU (ε/2) hε2
  -- BadCount の密度1：最終的に BadCount ≤ (ε/2)·X^2
  have hBC := eventually_badcount_le_eps' (hη := hε2)
  -- X≥2 を同時に課す（残りの議論で 1 mod X が 1 になるように）
  let ev2 := Filter.eventually_atTop.2 ⟨2, fun k hk => hk⟩
  -- 3つを合流し、各 X に関する仮定を取り出す
  filter_upwards [hU', hBC, ev2] with X hU_X hBC_X hXge2
  -- 均一性に M:=X, t:=1 を突っ込む（M∈[1,X] は X≥1 で可）
  have hM : 1 ≤ X ∧ X ≤ X := ⟨(Nat.le_trans (by norm_num : 1 ≤ 2) hXge2), le_rfl⟩
  have hResid :
      ((@Finset.filter (ℕ × ℕ)
          (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
          (fun p => Classical.propDecidable
              (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
          ((Finset.range (X+1)).product (Finset.range (X+1)))).card : ℝ)
      ≤ (BadCount 0.435 X : ℝ) / X + (ε/2) * X :=
    by
      have := hU_X X hM (1 : ℤ)
      simpa using this
  -- 対角の b↦(b-1,b) は residue t=1 の集合へ単射に移る：card で抑える
  -- 抜き出した補題を使って画像が含まれることを示す（簡潔化）
  have hDiag_le_residue : (diagBadCount 0.435 X : ℝ) ≤
      ((@Finset.filter (ℕ × ℕ)
          (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
          (fun p => Classical.propDecidable
              (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
          ((Finset.range (X+1)).product (Finset.range (X+1)))).card : ℝ) := by
    classical
    let S := (Finset.Icc 1 X).filter (fun b => is_bad_a 0.435 X b (b-1))
    let g := fun b => (b-1, b)
    let ranges_prod := (Finset.range (X + 1)).product (Finset.range (X + 1))
    have img_sub : (S.image g) ⊆ (@Finset.filter (ℕ × ℕ)
      (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
      (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
      ranges_prod) := by
      intro y hy
      obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.1 hy
      exact mem_image_g_mem_residue hbS hXge2
    have finj : Function.Injective g := fun x y h => congrArg Prod.snd h
    have img_eq_S : (S.image g).card = S.card := Finset.card_image_of_injective S finj
    have img_card_le_res : (S.image g).card ≤ (@Finset.filter (ℕ × ℕ)
      (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
      (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
      ((Finset.range (X+1)).product (Finset.range (X+1)))).card := by
      exact Finset.card_le_card img_sub
    have S_card_le_res : S.card ≤ (@Finset.filter (ℕ × ℕ)
      (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
      (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
      ((Finset.range (X+1)).product (Finset.range (X+1)))).card := by
      rwa [img_eq_S] at img_card_le_res
    have hS_eq : S.card = diagBadCount 0.435 X := rfl
    have hS_le : (S.card : ℝ) ≤ ((@Finset.filter (ℕ × ℕ)
      (fun p => ((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p)
      (fun p => Classical.propDecidable (((p.2 : ℤ) - (p.1 : ℤ)) % X = (1 : ℤ) ∧ BadPair 0.435 X p))
      ((Finset.range (X+1)).product (Finset.range (X+1)))).card : ℝ) := by
      exact_mod_cast S_card_le_res
    rw [hS_eq] at hS_le
    exact hS_le
  -- まとめ：diag ≤ residue ≤ BadCount/X + (ε/2)X ≤ (ε/2)X + (ε/2)X = εX

  have one_le_X : 1 ≤ X := by linarith [hXge2]
  -- X > 0 so we can divide inequalities by X when working over ℝ
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) one_le_X)

  -- From hBC_X : ↑(BadCount) ≤ (ε/2) * X^2, divide by X>0 to get BadCount/X ≤ (ε/2) X
  have h_div_bound : (BadCount 0.435 X : ℝ) / (X : ℝ) ≤ (ε/2) * (X : ℝ) := by
    have hden : (X : ℝ) ≠ 0 := (ne_of_gt hXpos)
    calc
      (BadCount 0.435 X : ℝ) / (X : ℝ) = (BadCount 0.435 X : ℝ) * (1 / (X : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ ((ε/2) * (X : ℝ) ^ 2) * (1 / (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hBC_X (le_of_lt (one_div_pos.2 hXpos))
      _ = (ε/2) * (X : ℝ) := by field_simp [hden, pow_two]

  -- combine diag ≤ residue ≤ BadCount/X + (ε/2)X and the division bound to finish
  have h_middle : (diagBadCount 0.435 X : ℝ) ≤ (BadCount 0.435 X : ℝ) / (X : ℝ) + (ε/2) * (X : ℝ) :=
    le_trans hDiag_le_residue hResid

  have h_sum : (BadCount 0.435 X : ℝ) / (X : ℝ) + (ε/2) * (X : ℝ) ≤ (ε/2) * (X : ℝ) + (ε/2) * (X : ℝ) :=
    add_le_add h_div_bound (le_refl ((ε/2) * (X : ℝ)))

  have h_final_le : (diagBadCount 0.435 X : ℝ) ≤ (ε/2) * (X : ℝ) + (ε/2) * (X : ℝ) :=
    le_trans h_middle h_sum

  have : (ε/2) * (X : ℝ) + (ε/2) * (X : ℝ) = ε * (X : ℝ) := by ring
  change ↑(diagBadCount 0.435 X) ≤ ε * ↑X
  · calc
      (diagBadCount 0.435 X : ℝ) ≤ (ε/2) * (X : ℝ) + (ε/2) * (X : ℝ) := h_final_le
      _ = ε * (X : ℝ) := by ring

-- ## Adjacent 族の定義と性質
-- ABC/Adjacent: quality を正規定義し、対角で a.e. に q ≤ 1+ε を立てる

/-- Adjacent triple （n, n+1, 2n+1） -/
def Adj (n : ℕ) : Triple :=
  Triple.mk n (n + 1) (2 * n + 1) (by ring) (coprime_succ n)

def Adj' (n : ℕ) : Triple :=
  Triple.mk n (n + 1) (n + (n + 1)) (by ring) (coprime_succ n)

@[simp]
lemma Adj_eq_Adj' (n : ℕ) : Adj n = Adj' n := by
  dsimp [Adj, Adj']
  have h : 2 * n + 1 = n + (n + 1) := by ring
  -- rewrite the differing component and finish by simplification
  simp [h]

/- provide decidability for Bad on Adj(n) globally -/
noncomputable instance Bad_adj_decidable (δ : ℝ) : ∀ n, Decidable (Bad δ (Adj n)) :=
  fun n => Classical.dec (Bad δ (Adj n))

/- Provide a global DecidablePred for the specific δ = 0.435 so Finset.filter uses a definitional instance -/
noncomputable instance Bad_adj_decidablePred : DecidablePred fun n => Bad 0.435 (Adj n) :=
  fun n => Bad_adj_decidable 0.435 n


end ABC
