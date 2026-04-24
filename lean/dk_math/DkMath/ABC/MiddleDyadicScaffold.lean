/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.Basic.Nat
import DkMath.ABC.AdjacentBadDensity

#print "file: DkMath.ABC.MiddleDyadicScaffold"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open DkMath.Basic.Nat
open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/- # Dyadic scaffold for `MiddleBand_exception_bound'`

This file provides a *clean combinatorial shell* to turn per-block bounds into
a global bound of the form `BadCount θ X ≤ C · X^(α + ε)` for large `X`.
The only analytic input is a per-block bound hypothesis.
-/

/-- Abstract “index set up to `X`” for the middle band. Replace by your actual set. -/
def MidIdx (X : ℕ) : Finset ℕ :=
  -- placeholder: typically {n ∈ Icc 1 X | n ∈ middle_band θ } as a filter
  (Finset.Icc 1 X)

/-- Dyadic block at level k (abstract; replace by your actual middle-band slice). -/
def MidBlock (k : ℕ) (X : ℕ) : Finset ℕ :=
  -- e.g. n with 2^k ≤ n < min(2^{k+1}, X), additionally intersect middle-band predicate.
  let L := (2:ℕ)^k
  let U := min ((2:ℕ)^(k+1) - 1) X
  (Finset.Icc L U)

/-- Simple covering property: indices up to `X` are covered by the union of blocks
    for k from 0 to ⌊log2 X⌋+1 (loose upper bound). You can strengthen as needed. -/
lemma MidIdx_subset_blocks (X : ℕ) :
  MidIdx X ⊆
    (Finset.range (Nat.log2 (X + 1) + 1)).biUnion (fun k => MidBlock k X) := by
  -- Soft over-cover; correctness for our purpose is that every n ≤ X falls in some dyadic shell.
  -- A tight partition is not necessary; overlaps only help for an upper bound.
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
  -- choose k = log2(n) (with 0 guard)
  have hpos : 1 ≤ n := hn1
  have hk : Nat.log2 (n) ≤ Nat.log2 (X + 1) := by
    -- monotonicity of log2 on ℕ for 1 ≤ n ≤ X ≤ X+1
    -- #check Nat.log2_le_log2_of_le
    -- Nat.log2_le_log2_of_le {n X : ℕ} : 1 ≤ n → ∀ (hX : n ≤ X) (hX1 : X ≤ X + 1), n.log2 ≤ (X + 1).log2
    exact Nat.log2_le_log2_of_le hpos hnX (Nat.le_succ X)
  have hkin : Nat.log2 n ∈ Finset.range (Nat.log2 (X + 1) + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  -- show n ∈ MidBlock (log2 n) X
  have : n ∈ MidBlock (Nat.log2 n) X := by
    -- crude bounds: 2^{log2 n} ≤ n < 2^{log2 n + 1}
    -- #check pow_log2_le_self
    -- Nat.pow_log2_le_self {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.log 2 n ≤ n
    -- #check Nat.log2_eq_log_two
    -- Nat.log2_eq_log_two {n : ℕ} : n.log2 = Nat.log 2 n
    -- Nat.pow_log2_le_self は 2 ^ Nat.log 2 n ≤ n なので log2_eq_log_two で型を揃える -/
    have hL : (2:ℕ)^(Nat.log2 n) ≤ n := by
      -- #check Nat.pow_log2_le_self
      -- Nat.pow_log2_le_self {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.log 2 n ≤ n
      have : Nat.log2 n = Nat.log 2 n := Nat.log2_eq_log_two
      rw [this]
      exact Nat.pow_log2_le_self hpos
    have hU : n ≤ (2:ℕ)^(Nat.log2 n + 1) - 1 := by
      -- n < 2^{log2 n + 1} ⇒ n ≤ 2^{...}-1
      -- n < 2^{log2 n + 1} は 2^{log2 n} ≤ n < 2^{log2 n + 1} の性質から導ける -/
      have : n < (2:ℕ)^(Nat.log2 n + 1) := by
        -- 2^{log2 n} ≤ n < 2^{log2 n + 1} を直接示す
        have h1 : (2:ℕ)^(Nat.log2 n) ≤ n := by
          rw [Nat.log2_eq_log_two]
          exact Nat.pow_log2_le_self hpos
        have h2 : n < (2:ℕ)^(Nat.log2 n + 1) := by
          -- 2^{log2 n + 1} = 2 * 2^{log2 n}
          rw [pow_add, pow_one]
          -- n ≥ 1, 2^{log2 n} ≤ n, so 2^{log2 n + 1} = 2 * 2^{log2 n} > n
          have hbase : 2 * (2:ℕ)^(Nat.log2 n) > n := by
            -- 2^{log2 n} ≤ n < 2 * 2^{log2 n}
            have h_lower : (2:ℕ)^(Nat.log2 n) ≤ n := by
              rw [Nat.log2_eq_log_two]
              exact Nat.pow_log2_le_self hpos
            have h_upper : n < 2 * (2:ℕ)^(Nat.log2 n) := by
              -- n < 2 * 2^{log2 n} follows from the definition of log2
              rw [Nat.log2_eq_log_two]
              -- By definition of Nat.log2, 2 ^ Nat.log2 n ≤ n < 2 ^ (Nat.log 2 n + 1) for n ≥ 1 -/
              have hlog := Nat.log2_spec hpos
              -- 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n
              rw [pow_add, pow_one] at hlog
              rw [mul_comm] at hlog
              exact hlog.2
            exact h_upper
          rw [mul_comm]
          exact hbase
        exact h2
      exact Nat.le_pred_of_lt this
    -- min with X preserves ≤ if needed
    have : n ∈ Finset.Icc ((2:ℕ)^(Nat.log2 n)) (min ((2:ℕ)^(Nat.log2 n + 1) - 1) X) := by
      refine Finset.mem_Icc.mpr ?_
      constructor
      · exact hL
      · exact le_min hU hnX
    simpa [MidBlock] using this
  -- bind membership
  exact Finset.mem_biUnion.mpr ⟨_, hkin, by simpa⟩

/-- Dyadic blocks are pairwise disjoint: for distinct levels their index intervals do not overlap. -/
lemma MidBlock_pairwise_disjoint (X : ℕ) :
  ∀ i j, i ∈ Finset.range (Nat.log2 (X + 1) + 1) → j ∈ Finset.range (Nat.log2 (X + 1) + 1) →
    i ≠ j → Disjoint (MidBlock i X) (MidBlock j X) := by
  let K := Nat.log2 (X + 1) + 1
  intro i j hi hj hij
  by_cases hlt : i < j
  · -- case i < j: show upper end of block i is < lower end of block j
    refine Finset.disjoint_left.2 fun n hn_i hn_j => by
      rcases (Finset.mem_Icc.mp hn_i) with ⟨_li_le_n, n_le_ui⟩
      rcases (Finset.mem_Icc.mp hn_j) with ⟨lj_le_n, _n_le_uj⟩
      -- i+1 ≤ j gives 2^(i+1) ≤ 2^j, so (2^(i+1)-1) < 2^j
      have i1 : i + 1 ≤ j := Nat.succ_le_of_lt hlt
      have pow_le := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) i1
      have lt_pred_pow : (2:ℕ)^(i + 1) - 1 < (2:ℕ)^(i + 1) := by
        have hpos : 0 < (2:ℕ)^(i + 1) := by apply Nat.pow_pos; norm_num
        have hne : (2:ℕ)^(i + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        calc
          (2:ℕ)^(i + 1) - 1 = Nat.pred ((2:ℕ)^(i + 1)) := by rw [Nat.pred_eq_sub_one]
          _ < (2:ℕ)^(i + 1) := Nat.pred_lt hne
      have upper_lt_2j : (min ((2:ℕ)^(i + 1) - 1) X) < (2:ℕ)^j := by
        calc
          (min ((2:ℕ)^(i + 1) - 1) X) ≤ (2:ℕ)^(i + 1) - 1 := min_le_left _ _
          _ < (2:ℕ)^(i + 1) := lt_pred_pow
          _ ≤ (2:ℕ)^j := pow_le
      -- n ≤ upper bound of i-block and that upper bound < 2^j, so n < 2^j,
      -- but lj_le_n (the lower bound for the j-block) gives 2^j ≤ n, contradiction.
      have hn_lt_2j : n < (2:ℕ)^j := lt_of_le_of_lt n_le_ui upper_lt_2j
      exact lt_irrefl n (lt_of_lt_of_le hn_lt_2j lj_le_n)
  · -- case j < i: symmetric
    have hji : j < i := by
      have hj_le_i : j ≤ i := le_of_not_gt hlt
      exact lt_of_le_of_ne hj_le_i (Ne.symm hij)
    refine Finset.disjoint_left.2 fun n hn_i hn_j => by
      rcases (Finset.mem_Icc.mp hn_j) with ⟨_lj_le_n, n_le_uj⟩
      rcases (Finset.mem_Icc.mp hn_i) with ⟨_li_le_n, _n_le_ui⟩
      -- j+1 ≤ i gives 2^(j+1) ≤ 2^i, so (2^(j+1)-1) < 2^i
      have j1 : j + 1 ≤ i := Nat.succ_le_of_lt hji
      have pow_le := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) j1
      have lt_pred_pow' : (2:ℕ)^(j + 1) - 1 < (2:ℕ)^(j + 1) := by
        have hpos : 0 < (2:ℕ)^(j + 1) := by apply Nat.pow_pos; norm_num
        have hne : (2:ℕ)^(j + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        calc
          (2:ℕ)^(j + 1) - 1 = Nat.pred ((2:ℕ)^(j + 1)) := by rw [Nat.pred_eq_sub_one]
          _ < (2:ℕ)^(j + 1) := Nat.pred_lt hne
      have min_lt_2i : (min ((2:ℕ)^(j + 1) - 1) X) < (2:ℕ)^i := by
        calc
          (min ((2:ℕ)^(j + 1) - 1) X) ≤ (2:ℕ)^(j + 1) - 1 := min_le_left _ _
          _ < (2:ℕ)^(j + 1) := lt_pred_pow'
          _ ≤ (2:ℕ)^i := pow_le
      -- n ≤ upper bound of j-block and that upper bound < 2^i, so n < 2^i,
      -- and from hn_i we have the lower bound 2^i ≤ n, contradiction.
      have hn_lt_2i : n < (2:ℕ)^i := lt_of_le_of_lt n_le_uj min_lt_2i
      have two_i_le_n : (2:ℕ)^i ≤ n := (Finset.mem_Icc.mp hn_i).1
      exact lt_irrefl n (lt_of_lt_of_le hn_lt_2i two_i_le_n)

/-- Project’s counting function restricted to a finite set `S`. Replace with your actual `BadCount`. -/
def BadCountOn (_ : ℝ) (S : Finset ℕ) : ℕ :=
  -- cardinality of “bad” indices in S; in your project this is a filter/predicate.
  S.card  -- placeholder; swap for `(S.filter isBad).card`

/-- Subadditivity over unions (very soft, with overlaps). -/
lemma BadCountOn_bind_le (θ : ℝ) (X : ℕ) :
  BadCountOn θ (MidIdx X) ≤
    ∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), BadCountOn θ (MidBlock k X) := by
  -- Using the crude cover `MidIdx ⊆ ⋃ blocks` and counting measure,
  -- we can bound by the sum over blocks (overlaps only increase RHS).
  -- Implement by pointwise counting or by a simple `card_le_sum_card_filter` pattern.
  -- For now we present a simple “card ≤ sum of cards of images” argument.
  -- Replace with your project’s monotonicity lemma: `BadCountOn θ` is monotone in `S`.
  have hcov := MidIdx_subset_blocks X
  -- compare cards: #(MidIdx X) ≤ # (⋃_k MidBlock k X) ≤ sum_k #(MidBlock k X)
  have h1 : (MidIdx X).card ≤ ((Finset.range (Nat.log2 (X + 1) + 1)).biUnion fun k => MidBlock k X).card :=
    Finset.card_le_card hcov
  have : ((Finset.range (Nat.log2 (X + 1) + 1)).biUnion fun k => MidBlock k X).card
    ≤ ∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), (MidBlock k X).card := by
    -- general inequality: card (biUnion f) ≤ sum card (f i)
      exact Finset.card_biUnion_le
  calc
    BadCountOn θ (MidIdx X) = (MidIdx X).card := by simp [BadCountOn]
    _ ≤ ((Finset.range (Nat.log2 (X + 1) + 1)).biUnion fun k => MidBlock k X).card := h1
    _ ≤ ∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), (MidBlock k X).card := this
    _ = ∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), BadCountOn θ (MidBlock k X) := by simp [BadCountOn]

lemma BadCountOn_mono (θ : ℝ) {S T : Finset ℕ} (hST : S ⊆ T) :
  BadCountOn θ S ≤ BadCountOn θ T := by
  simp only [BadCountOn]
  exact Finset.card_le_card hST

/-- Hypothesis schema: per-dyadic-block bound with an explicit exponent α and ε-buffer.
    This is *exactly* where you plug `Block_Janson_*` estimates. -/
structure BlockBound (θ : ℝ) where
  (α : ℝ)
  (hα : 0 < α)  -- exponent baseline
  (bound :
    ∀ (ε : ℝ), 0 < ε →
    ∃ (k0 : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ ⦃X k⦄, X ≥ (2:ℕ)^k → k ≥ k0 →
        (BadCountOn θ (MidBlock k X) : ℝ)
          ≤ C * ((2:ℕ)^k : ℝ)^(α + ε))

/-- Geometric-sum helper: ∑_{k ≤ K} 2^{(α+ε)k} ≤ C' · X^{α+ε} with K ~ log₂ X. -/
lemma geom_sum_pow_two_le (α ε : ℝ) (h : 0 < α + ε) :
  ∀ (X : ℕ), 1 ≤ X →
    (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
      ((2:ℝ) ^ (α + ε))^k) ≤
      ((2:ℝ)^(3 * (α + ε)) / ((2:ℝ)^(α + ε) - 1)) * (X : ℝ)^(α + ε) := by
  -- 要求を 1 ≤ X に限定して X = 0 の矛盾を回避する -/
  intro X hX1
  set q := (2:ℝ)^(α + ε) with hqdef
  have hqpos : 1 < q := by
    have : (2:ℝ) > 1 := by norm_num
    exact Real.one_lt_rpow this h
  have q_ne1 : q ≠ 1 := by linarith [hqpos]
  have hsum_eq : (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), q ^ k) = (q ^ (Nat.log2 (X + 1) + 1) - 1) / (q - 1) := by
    let n := Nat.log2 (X + 1) + 1
    -- prove (q - 1) * ∑_{k=0}^{n-1} q^k = q^n - 1 by induction on n
    have hmul : (q - 1) * (∑ k ∈ Finset.range n, q ^ k) = q ^ n - 1 := by
      induction n with
      | zero => simp [Finset.range]
      | succ n ih =>
        -- sum_range_succ: ∑_{k=0}^{n} f k = (∑_{k=0}^{n-1} f k) + f n
        simp only [ne_eq, Finset.range, Finset.sum_mk, Multiset.range_succ, Finset.mk_cons,
          Finset.cons_eq_insert, Finset.mem_mk, Multiset.mem_range, lt_self_iff_false,
          not_false_eq_true, Finset.sum_insert, mul_add] at *
        rw [ih]
        simp [pow_succ]
        ring
    -- q > 1 implies q - 1 ≠ 0, so divide both sides to get the usual closed form
    have q_ne0 : q - 1 ≠ 0 := by linarith [hqpos]
    have : ∑ k ∈ Finset.range n, q ^ k = (q ^ n - 1) / (q - 1) := by
      -- swap the multiplication order to match `eq_div_of_mul_eq`'s expected shape
      rw [mul_comm] at hmul
      exact eq_div_of_mul_eq q_ne0 hmul
    simpa [n] using this
  have hsum : (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), q ^ k) ≤ q ^ (Nat.log2 (X + 1) + 1) / (q - 1) := by
    rw [hsum_eq]
    let n := Nat.log2 (X + 1) + 1
    have hden_pos : 0 < q - 1 := by linarith
    have hnum_le : q ^ n - 1 ≤ q ^ n := by linarith
    -- divide both sides by the positive denominator q - 1 by multiplying with 1 / (q - 1)
    calc
    (q ^ n - 1) / (q - 1) = (q ^ n - 1) * (1 / (q - 1)) := by rw [div_eq_mul_one_div]
    _ ≤ q ^ n * (1 / (q - 1)) := by
      apply mul_le_mul_of_nonneg_right
      · exact hnum_le
      · exact le_of_lt (one_div_pos.mpr hden_pos)
    _ = q ^ n / (q - 1) := by
      rw [←div_eq_mul_one_div]
  -- q^(K+1) を 2^{3*(α+ε)} * X^{α+ε} で上界する -/
  have h2K1 : (2:ℕ) ^ (Nat.log2 (X + 1) + 1) ≤ 4 * X := by
    -- use 1 ≤ X + 1 (holds for all X) so Nat.pow_log2_le_self applies to X + 1
    have : (2:ℕ) ^ (Nat.log2 (X + 1)) ≤ X + 1 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log2_le_self (Nat.succ_pos X)
    calc
      (2:ℕ) ^ (Nat.log2 (X + 1) + 1) = 2 * (2:ℕ) ^ Nat.log2 (X + 1) := by simp [pow_add, pow_one, mul_comm]
      _ ≤ 2 * (X + 1) := by apply Nat.mul_le_mul_left; exact this
      _ ≤ 2 * (2 * X) := by linarith [hX1]
      _ = 4 * X := by ring
  have hpow_bound : q ^ (Nat.log2 (X + 1) + 1) ≤ (2:ℝ) ^ (2 * (α + ε)) * (X : ℝ) ^ (α + ε) := by
    let n := Nat.log2 (X + 1) + 1
    -- q = 2^(α+ε).  We rewrite q^n = 2^{(α+ε)*n} and then as (2^n)^(α+ε),
    -- afterwards bound 2^n ≤ 4 * X and apply monotonicity of rpow.
    have h2pos : 0 < (2:ℝ) := by
      norm_num
    have hbase_nonneg : 0 ≤ (2:ℝ) ^ (n : ℝ) := by
      -- 2 > 0 implies (2 : ℝ) ^ n > 0; use the exponential representation to avoid `Real.rpow_pos`
      -- 2 > 0 を明示して Real.rpow_def_of_pos の型を合わせる -/
      have : (2:ℝ) ^ (n : ℝ) = Real.exp (↑n * Real.log 2) :=
        by rw [Real.rpow_def_of_pos (by exact zero_lt_two) (n : ℝ), mul_comm]
      rw [this]
      apply le_of_lt
      exact Real.exp_pos ((n : ℝ) * Real.log (2:ℝ))
    calc
      q ^ n = (2:ℝ) ^ ((α + ε) * (n : ℝ)) := by
        rw [hqdef]; simp [Real.rpow_mul]
      _ = ((2:ℝ) ^ (n : ℝ)) ^ (α + ε) := by
        have eq := Real.rpow_mul (le_of_lt h2pos) (n : ℝ) (α + ε)
        rw [mul_comm] at eq
        exact eq
      _ ≤ ((4 : ℝ) * (X : ℝ)) ^ (α + ε) := by
        -- (2^n : ℝ) ≤ 4 * X by h2K1 (cast to ℝ), then raise both sides to (α+ε) ≥ 0
        apply Real.rpow_le_rpow hbase_nonneg
          (by exact_mod_cast h2K1)
          (by linarith [h])
      _ = (2:ℝ) ^ (2 * (α + ε)) * (X : ℝ) ^ (α + ε) := by
        -- (4 * X)^(α+ε) = 4^(α+ε) * X^(α+ε) = (2^2)^(α+ε) * X^(α+ε) = 2^(2*(α+ε)) * X^(α+ε) -/
        rw [mul_comm]
        rw [mul_comm]
        -- (a * b)^p = a^p * b^p を使う -/
        rw [mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) (by linarith [hX1])]
        -- 4 ^ (α + ε) = (2 ^ 2) ^ (α + ε) = 2 ^ (2 * (α + ε)) じゃ -/
        rw [Real.rpow_mul (by norm_num)]
        ring_nf
  calc
    (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), q ^ k)
        ≤ q ^ (Nat.log2 (X + 1) + 1) / (q - 1) := hsum
    _ ≤ ((2:ℝ)^(3 * (α + ε)) / ((2:ℝ)^(α + ε) - 1)) * (X : ℝ)^(α + ε) := by
      -- 中間不等式を hpow_bound から直接導き、分母 (q - 1) の正性を利用して整理する
      have hden_pos : 0 < q - 1 := by linarith
      let n := Nat.log2 (X + 1) + 1
      -- q^n ≤ 2^(2(α+ε)) * X^(α+ε) を (q-1) の逆数で掛けて両辺を比較する
      have hinv_nonneg : 0 ≤ (q - 1)⁻¹ := by
        apply le_of_lt
        exact inv_pos.mpr hden_pos
      have hdiv' : q ^ n / (q - 1) ≤ (2:ℝ) ^ (2 * (α + ε)) * (X : ℝ) ^ (α + ε) / (q - 1) :=
        mul_le_mul_of_nonneg_right hpow_bound hinv_nonneg
      -- さらに 2^(2p) ≤ 2^(2p) * q (q ≥ 1) を使って分子を増やし、目的の形にする
      have hq_ge1 : 1 ≤ q := by linarith [hqpos]
      have h_nonneg : 0 ≤ (2:ℝ) ^ (2 * (α + ε)) := by positivity
      have h2pow_le := le_mul_of_one_le_right h_nonneg hq_ge1
      -- (X^(α+ε) / (q - 1)) が非負であることを確認して、それを掛ける
      have hX_nonneg : 0 ≤ (X : ℝ) ^ (α + ε) := by
        have hXpos : 0 < (X : ℝ) := by norm_cast
        exact le_of_lt (Real.rpow_pos_of_pos hXpos (α + ε))
      have hdiv_term_nonneg : 0 ≤ (X : ℝ) ^ (α + ε) / (q - 1) := by
        apply div_nonneg
        · exact hX_nonneg
        linarith [hden_pos]
      -- h2pow_le を (X^(α+ε) / (q - 1)) に掛けて、期待する形の不等号を得る
      have hstep : (2:ℝ) ^ (2 * (α + ε)) * (↑X ^ (α + ε) / (q - 1))
        ≤ (2:ℝ) ^ (3 * (α + ε)) / (q - 1) * ↑X ^ (α + ε) := by
        -- multiply the inequality 2^(2p) ≤ 2^(2p) * q by the nonnegative factor X^(p)/(q-1)
        have htmp := mul_le_mul_of_nonneg_right h2pow_le hdiv_term_nonneg
        -- rewrite the RHS using q = 2^(α+ε) to get the desired shape
        have heq1 : (2:ℝ) ^ (2 * (α + ε)) * q * (↑X ^ (α + ε) / (q - 1))
          = (2:ℝ) ^ (3 * (α + ε)) * (↑X ^ (α + ε) / (q - 1)) := by
          calc
            (2:ℝ) ^ (2 * (α + ε)) * q * (↑X ^ (α + ε) / (q - 1))
              = (2:ℝ) ^ (2 * (α + ε)) * (2:ℝ) ^ (α + ε) * (↑X ^ (α + ε) / (q - 1)) := by
                rw [hqdef]
            _ = (2:ℝ) ^ (2 * (α + ε) + (α + ε)) * (↑X ^ (α + ε) / (q - 1)) := by
                rw [← Real.rpow_add (by norm_num : 0 < (2:ℝ)) (2 * (α + ε)) (α + ε)]
            _ = (2:ℝ) ^ (3 * (α + ε)) * (↑X ^ (α + ε) / (q - 1)) := by
                congr
                ring
        have heq2 : (2:ℝ) ^ (3 * (α + ε)) * (↑X ^ (α + ε) / (q - 1))
          = (2:ℝ) ^ (3 * (α + ε)) / (q - 1) * ↑X ^ (α + ε) := by
          field_simp [q_ne1]
        rw [heq1, heq2] at htmp
        exact (by simpa [mul_div_assoc] using htmp)
      -- hdiv' の右辺の括弧付けを整えた中間不等式を導出し、hstep と結合する
      have hmid : q ^ n / (q - 1) ≤ (2:ℝ) ^ (2 * (α + ε)) * (↑X ^ (α + ε) / (q - 1)) := by
        calc
          q ^ n / (q - 1) ≤ (2:ℝ) ^ (2 * (α + ε)) * (X : ℝ) ^ (α + ε) / (q - 1) := hdiv'
          _ = (2:ℝ) ^ (2 * (α + ε)) * (↑X ^ (α + ε) / (q - 1)) := by rw [mul_div_assoc]
      exact le_trans hmid hstep


end DkMath.ABC
