/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC005

#print "file: DkMath.ABC.ABC006"

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

lemma pow_two_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  apply Nat.pow_le_pow_right
  · norm_num
  · exact h

lemma one_le_X_pow {X : ℕ} {s : ℝ} (hX : 1 ≤ X) (hs : 0 < s) : (1 : ℝ) ≤ (X : ℝ) ^ s :=
  Real.one_le_rpow (by exact_mod_cast hX) (le_of_lt hs)

lemma MidBlock_card_le_pow_head (k k0 X : ℕ) (hk : k < k0) :
  (MidBlock k X).card ≤ 2 ^ (k0 + 1) := by
  -- MidBlock k X ⊆ range (2^(k0+1)) and apply card_le_card
  have hsub : (MidBlock k X) ⊆ Finset.range (2 ^ (k0 + 1)) := by
    intro n hn
    -- expand MidBlock into Icc to be robust to MidBlock implementation
    have hnIcc : n ∈ Finset.Icc (2 ^ k) (Nat.min ((2:ℕ) ^ (k + 1) - 1) X) := by
      simpa [MidBlock] using hn
    rcases Finset.mem_Icc.mp hnIcc with ⟨_hL, hU_min⟩
    have n_le_upper : n ≤ 2 ^ (k + 1) - 1 := le_trans hU_min (Nat.min_le_left _ _)
    have lt_pred : (2 ^ (k + 1) - 1) < 2 ^ (k + 1) := by
      have hpos : 0 < 2 ^ (k + 1) := by apply Nat.pow_pos; norm_num
      exact Nat.pred_lt (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by norm_num) : _))
    have hlt : n < 2 ^ (k + 1) := Nat.lt_of_le_of_lt n_le_upper lt_pred
    have hpow : 2 ^ (k + 1) ≤ 2 ^ (k0 + 1) := by
      apply Nat.pow_le_pow_right
      · norm_num
      · exact Nat.succ_le_succ (Nat.le_of_lt hk)
    exact Finset.mem_range.2 (lt_of_lt_of_le hlt hpow)
  simpa [Finset.card_range] using Finset.card_le_card hsub

/--
head_absorb は、実数 θ, α, ε と自然数 k0 に対し、α + ε > 0 の仮定の下で成り立つ上界に関する定理です。
存在する自然数 X0 と非負実数 C により、任意の自然数 X（1 ≤ X かつ X ≥ X0）について
Finset.range k0 上の和
  ∑_{k < k0} (BadCountOn θ (MidBlock k X) : ℝ)
が C * X^(α + ε) 以下に抑えられることを主張します。

要点:
- hpos : 0 < α + ε により冪指数が正であることを保証します。
- 結論は「ある X0 と C が存在する」という形の逐次的上界であり、
  十分大きな X に対して和の寄与が多項式的に抑えられることを示します。
- BadCountOn, MidBlock の具体的意味や振る舞いは文脈依存ですが、
  本定理はそれらの合計が指定した次数で制御可能であることを利用するための補題的結果です。

利用上の注意:
- 仮定に X ≥ 1 を含めているため X = 0 は考慮されません。
- C は非負であるが必ずしも正とは限らない点に注意してください。
- 実際の C, X0 の取り方は BadCountOn や MidBlock に関する追加の評価に依存します。
- 証明では通常、各項の既知の上界を集約して全体の次数的評価を得る手法が用いられます。
- この結果は「ヘッド部分の吸収（head absorb）」と呼ばれ、全体の主要な成長項に比べて
  ヘッドの寄与が無視できることを示すのに有用です。
-/
theorem head_absorb (θ α ε : ℝ) (hpos : 0 < α + ε) (k0 : ℕ) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (Finset.sum (Finset.range k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ)) ≤ C * (X : ℝ)^(α + ε) := by
  -- Very short, robust proof: each MidBlock k X has cardinality ≤ 2^(k0+1), so
  -- the finite sum is bounded by k0 * 2^(k0+1), independent of X. Since X^(α+ε) ≥ 1
  -- for X ≥ 1, the desired inequality follows with X0 = 1.
  -- Use a crude uniform bound: for any k < k0, MidBlock k X ⊆ range (2 ^ (k0 + 1)), so
  -- (MidBlock k X).card ≤ 2^(k0+1). Therefore the finite sum over k < k0 is ≤ k0 * 2^(k0+1).
  -- Since X ≥ 1 and α + ε > 0 we have 1 ≤ X^(α+ε), so the constant can be absorbed.
  let C := (k0 : ℝ) * (2 ^ (k0 + 1) : ℝ)
  use 1, C
  constructor
  · have hk0_nonneg : 0 ≤ (k0 : ℝ) := by norm_cast; exact Nat.cast_nonneg k0
    have hpow_nonneg : 0 ≤ (2 ^ (k0 + 1) : ℝ) := by norm_cast; exact Nat.cast_nonneg (2 ^ (k0 + 1))
    exact mul_nonneg hk0_nonneg hpow_nonneg
  intro X h1 _
  -- Work at the integer level first to avoid typeclass inference issues.
  -- Work with BadCountOn directly (it equals the card of the set) to keep types ℕ.
  have nat_sum_le : (Finset.sum (Finset.range k0) fun k => BadCountOn θ (MidBlock k X))
    ≤ k0 * 2 ^ (k0 + 1) := by
    -- First bound the sum by the sum of the constant 2^(k0+1) over the same range.
    have hsum_le : (Finset.sum (Finset.range k0) fun k => BadCountOn θ (MidBlock k X))
      ≤ Finset.sum (Finset.range k0) fun _ => 2 ^ (k0 + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk_lt : k < k0 := (Finset.mem_range.mp hk)
      -- show per-k: BadCountOn θ (MidBlock k X) ≤ 2^(k0+1)
      have hsub : (MidBlock k X) ⊆ Finset.range (2 ^ (k0 + 1)) := by
        intro n hn
        rcases Finset.mem_Icc.mp hn with ⟨_hL, hUmin⟩
        have n_le_upper : n ≤ 2 ^ (k + 1) - 1 := le_trans hUmin (Nat.min_le_left _ _)
        have lt_pred : (2 ^ (k + 1) - 1) < 2 ^ (k + 1) := by
          have hpos : 0 < 2 ^ (k + 1) := by apply Nat.pow_pos; norm_num
          exact Nat.pred_lt (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by norm_num) : _))
        have hlt : n < 2 ^ (k + 1) := Nat.lt_of_le_of_lt n_le_upper lt_pred
        have hpow : 2 ^ (k + 1) ≤ 2 ^ (k0 + 1) := by
          apply Nat.pow_le_pow_right
          · norm_num
          · exact Nat.succ_le_succ (Nat.le_of_lt hk_lt)
        exact Finset.mem_range.2 (lt_of_lt_of_le hlt hpow)
      have hcard_bound := Finset.card_le_card hsub
      simpa [Finset.card_range] using hcard_bound
    -- simplify the sum of constants to k0 * 2^(k0+1)
    simpa [Finset.sum_const, Finset.card_range] using hsum_le
  -- Cast to ℝ and finish by absorbing X^(α+ε) ≥ 1
  have real_sum_le : (Finset.sum (Finset.range k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ))
    ≤ (k0 : ℝ) * (2 ^ (k0 + 1) : ℝ) := by exact_mod_cast nat_sum_le
  have one_le : 1 ≤ (X : ℝ) ^ (α + ε) := Real.one_le_rpow (by exact_mod_cast h1) (le_of_lt hpos)
  have C_nonneg : 0 ≤ (k0 : ℝ) * (2 ^ (k0 + 1) : ℝ) := by
    norm_cast
    apply mul_nonneg
    · exact Nat.cast_nonneg k0
    · exact Nat.cast_nonneg (2 ^ (k0 + 1))
  have real_bound : (k0 : ℝ) * (2 ^ (k0 + 1) : ℝ) ≤ (k0 : ℝ) * (2 ^ (k0 + 1) : ℝ) * (X : ℝ)^(α + ε) := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left one_le C_nonneg
  exact le_trans real_sum_le real_bound

/--
尾部の集計境界 (tail geometric bound)。

概要:
  H : BlockBound θ によって与えられる各ブロックの上界を用いて、
  ある定数 k0, X0, 非負の定数 Ctail が存在し、
  任意の X ≥ X0 に対して k ≥ k0 の項だけを合計したダイアディック尾部和が
  Ctail * X^(α + ε) で一様に抑えられることを主張する定理。

引数:
  - H : BlockBound θ
      ブロックごとの評価を与える仮定。特に H.α を用いる。
  - ε : ℝ, hε : 0 < ε
      正の余分の指数。任意の正εに対して成り立つ。

結論:
  ある自然数 k0, X0 と実数 Ctail ≥ 0 が存在し、
  任意の自然数 X (1 ≤ X かつ X ≥ X0) に対して
  Finset.range (Nat.log2 (X + 1) + 1) にわたる和のうち k ≥ k0 の項だけを足したものが
  Ctail * (X : ℝ)^(H.α + ε) 以下になる。
  ここで和の項は (BadCountOn θ (MidBlock k X) : ℝ) とする。

証明の方針（概観）:
  - H による各ブロックの個別評価と、k に対して減衰する幾何級数的因子を組み合わせる。
  - k0 を十分大きく選ぶことで尾部の寄与を幾何級数和で抑え、X^(α+ε) の形にまとめる。
  - Nat.log2 (X+1) によって和は有限和となるため、上界付けが可能になる。
-/
-- Tail aggregation: bound the dyadic tail (k ≥ k0) by a geometric-sum factor times X^(α+ε).
theorem tail_geom_bound' {θ : ℝ} (H : BlockBound θ) (ε : ℝ) (hε : 0 < ε) :
  ∃ (k0 : ℕ) (X0 : ℕ) (Ctail : ℝ), 0 ≤ Ctail ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
  Finset.sum (Finset.range (Nat.log2 (X + 1) + 1)) (fun k => (if k ≥ k0 then ((BadCountOn θ (MidBlock k X) : ℝ)) else (0 : ℝ)))
        ≤ Ctail * (X : ℝ)^(H.α + ε) := by
  -- Reuse the already-proved `dyadic_tail_bound` from MathlibHello/ABC.lean.
  obtain ⟨k0, Ctot, hC_nonneg, hbound⟩ := dyadic_tail_bound H ε hε
  -- hbound: ∀ X, 1 ≤ X → sum (filter (· ≥ k0) (range (log2 (X+1)+1))) BadCountOn ≤ Ctot * X^(α+ε)
  use k0, 1, Ctot
  constructor
  · exact hC_nonneg
  intro X h1 hXge
  let K := Nat.log2 (X + 1) + 1
  -- Convert the if-sum over `range K` to the filtered sum used by `dyadic_tail_bound`.
  let rangeK := Finset.range K
  -- Use the standard lemma `Finset.sum_subtype_eq_sum_filter` which states
  -- `∑ x in s.filter p, f x = ∑ x in s, if p x then f x else 0`.
  -- Rewriting backwards gives the desired equality between the if-sum and the filtered sum.
  have split : Finset.sum rangeK (fun k => (if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ)))
      = Finset.sum (rangeK.filter fun k => k ≥ k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ) := by
    -- `Finset.sum_filter` is the standard lemma: sum over s of (if p then f else 0) = sum over s.filter p of f
    rw [Finset.sum_filter]
  rw [split]
  exact hbound X (by exact_mod_cast h1)

/- Tail bound wrapper: reuse dyadic_tail_bound from ABC.lean -/
theorem tail_geom_bound {θ : ℝ} (H : BlockBound θ) (ε : ℝ) (hε : 0 < ε) :
  ∃ (k0 : ℕ) (Ctot : ℝ), 0 ≤ Ctot ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X →
      (Finset.sum (Finset.range (Nat.log2 (X + 1) + 1)) fun k =>
        if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ)) ≤ Ctot * (X : ℝ)^(H.α + ε) := by
  -- Delegate to the already-proved `dyadic_tail_bound` in `ABC.lean`.
  have := ABC.dyadic_tail_bound H ε hε
  -- dyadic_tail_bound has the shape: ∃ k0 C ≥0, ∀ X, sum_{k ≥ k0}^{log2(X+1)} (BadCountOn ...) ≤ C * X^(α+ε)
  obtain ⟨k0, Ctot, hC_nonneg, hbound⟩ := this
  use k0, Ctot
  constructor; · exact hC_nonneg
  intro X h1
  -- Convert the conditional-sum over the full range into the filtered-sum form and apply hbound.
  rw [← Finset.sum_filter]
  apply hbound X h1

/--
θ に関する dyadic ブロックの合成に伴う「悪い」インデックスの個数に対する上界を与える補題。

概要:
与えられた実数 θ と仮定 H : BlockBound θ （特に実数指数 H.α を提供する）に対して，
任意の 0 < ε に対し，ある自然数 X0 と非負の定数 C が存在して，
すべての X ≥ X0 に対して次が成り立つ:
  (BadCountOn θ (MidIdx X) : ℝ) ≤ C * (X : ℝ)^(H.α + ε).
つまり，MidIdx に対応する「悪い」カウントは任意に小さな緩和 ε を許して
多項式的に X^(H.α+ε) 以下で抑えられる。

引数の意味:
- θ : ℝ — 対象となるパラメータ。
- H : BlockBound θ — θ に対するブロック境界の仮定（指数 α を含む）。
- ε : ℝ, 0 < ε — 任意の小さい正の余裕。

補足事項:
- 定数 C としきい X0 は θ, H, ε に依存して構わない。
- 結論は任意の ε>0 に対して成り立つため，成長率は実質的に X^(H.α+o(1)) であると解釈できる。
- 証明は dyadic 分割に基づくカウント推定と BlockBound からの局所的評価を組み合わせることで得られる。
- 自然数から実数へのキャスト (↑· : ℕ → ℝ) を用いて不等式を実数の文脈で述べている。
- 必要に応じて C や X0 の依存性やより厳密な定数評価を追加記述できる。
-/
theorem dyadic_compose (θ : ℝ) (H : BlockBound θ) :
  ∀ (ε : ℝ), 0 < ε →
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, X ≥ X0 →
      (BadCountOn θ (MidIdx X) : ℝ) ≤ C * (X : ℝ)^(H.α + ε) := by
  intro ε hε
  -- use the tail wrapper to get a dyadic tail threshold k0 and constant Ctail
  obtain ⟨k0, Ctail, hCtail_nonneg, htail⟩ := tail_geom_bound (H := H) ε hε
  -- use head_absorb to absorb the finite head k < k0 into a constant times X^(α+ε)
  obtain ⟨X0_head, Chead, hChead_nonneg, hhead⟩ := head_absorb (θ := θ) H.α ε (by linarith [H.hα]) k0
  -- choose a global X0 as the maximum of the head threshold and 1 (tail lemma assumes 1 ≤ X)
  let X0 := max X0_head 1
  use X0, (Chead + Ctail)
  constructor
  · -- nonnegativity of the combined constant
    apply add_nonneg <;> assumption
  intro X hXge
  -- start from the dyadic covering: BadCountOn MidIdx ≤ sum over blocks
  have hbind := BadCountOn_bind_le θ X
  -- split the full sum at nat-level, cast only when needed, and apply head/tail bounds
  let n := Nat.log2 (X + 1) + 1
  let sum_nat := Finset.sum (Finset.range n) fun k => BadCountOn θ (MidBlock k X)
  -- cast the integer inequality from BadCountOn_bind_le to reals
  have hbind_real : (BadCountOn θ (MidIdx X) : ℝ) ≤ (sum_nat : ℝ) := by exact_mod_cast hbind

  -- split nat-sum into head and tail (k < k0, k ≥ k0)
  let head_nat := Finset.sum (Finset.filter (fun k => k < k0) (Finset.range n)) fun k => BadCountOn θ (MidBlock k X)
  let tail_nat := Finset.sum (Finset.filter (fun k => ¬ (k < k0)) (Finset.range n)) fun k => BadCountOn θ (MidBlock k X)
  have sum_split_nat : sum_nat = head_nat + tail_nat :=
    (Finset.sum_filter_add_sum_filter_not (s := Finset.range n) (p := fun k => k < k0) (f := fun k => BadCountOn θ (MidBlock k X))).symm

  -- head_nat ≤ sum over range k0 (nat level)
  have hnat_nonneg : ∀ k ∈ Finset.range n, 0 ≤ BadCountOn θ (MidBlock k X) := by intro k _; exact Nat.zero_le (BadCountOn θ (MidBlock k X))
  have head_subset : Finset.filter (fun k => k < k0) (Finset.range n) ⊆ Finset.range k0 := by
    intro k hk; rcases Finset.mem_filter.1 hk with ⟨_, hklt⟩; exact Finset.mem_range.2 hklt
  have head_le_nat : head_nat ≤ Finset.sum (Finset.range k0) fun k => BadCountOn θ (MidBlock k X) :=
    Finset.sum_le_sum_of_subset_of_nonneg head_subset (fun k hk _ => Nat.zero_le (BadCountOn θ (MidBlock k X)))

  -- cast head and tail to reals in controlled steps
  have head_le_real : (head_nat : ℝ) ≤ (Finset.sum (Finset.range k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ)) := by
    exact_mod_cast head_le_nat

  have tail_eq_real : (tail_nat : ℝ) = Finset.sum (Finset.range n) fun k => if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ) := by
    -- tail_nat is definitionally the nat-sum over filter (¬ (k < k0)); cast that equality to reals
    have h_def : tail_nat = Finset.sum (Finset.filter (fun k => ¬ (k < k0)) (Finset.range n)) fun k => BadCountOn θ (MidBlock k X) := rfl
    have cast_sum : (tail_nat : ℝ) = Finset.sum (Finset.filter (fun k => ¬ (k < k0)) (Finset.range n)) fun k => (BadCountOn θ (MidBlock k X) : ℝ) := by exact_mod_cast h_def
    calc
      (tail_nat : ℝ) = Finset.sum (Finset.filter (fun k => ¬ (k < k0)) (Finset.range n)) fun k => (BadCountOn θ (MidBlock k X) : ℝ) := by exact cast_sum
      _ = Finset.sum (Finset.range n) fun k => if ¬ (k < k0) then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ) := by rw [← Finset.sum_filter]
      _ = Finset.sum (Finset.range n) fun k => if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ) := by
        apply Finset.sum_congr rfl; intro k hk; simp

  -- combine nat-level split (cast) with hbind_real
  have total_le_real : (BadCountOn θ (MidIdx X) : ℝ) ≤ (head_nat : ℝ) + (tail_nat : ℝ) := by
    calc
      (BadCountOn θ (MidIdx X) : ℝ) ≤ (sum_nat : ℝ) := hbind_real
      _ = (head_nat + tail_nat : ℕ) := by rw [sum_split_nat]
      _ = (head_nat : ℝ) + (tail_nat : ℝ) := by simp
  -- Now apply head_absorb and tail bound
  have h1 : 1 ≤ X := by exact (le_trans (le_max_right X0_head 1) hXge)
  have hX0_head : X ≥ X0_head := by exact (le_trans (le_max_left X0_head 1) hXge)
  have head_bound := hhead (by exact h1) (by exact hX0_head)
  have tail_bound := htail (by exact h1)
  have tail_le_real : (tail_nat : ℝ) ≤ Finset.sum (Finset.range n) fun k => if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ) :=
    Eq.le tail_eq_real
  calc
    (BadCountOn θ (MidIdx X) : ℝ)
      ≤ (head_nat : ℝ) + (tail_nat : ℝ) := total_le_real
    _ ≤ (Finset.sum (Finset.range k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ)) +
          Finset.sum (Finset.range n) fun k => if k ≥ k0 then (BadCountOn θ (MidBlock k X) : ℝ) else (0 : ℝ) := by
        exact (add_le_add head_le_real tail_le_real)
    _ ≤ Chead * (X : ℝ) ^ (H.α + ε) + Ctail * (X : ℝ) ^ (H.α + ε) := by apply add_le_add head_bound tail_bound
    _ = (Chead + Ctail) * (X : ℝ) ^ (H.α + ε) := by ring


end ABC
