/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Triple

#print "file: DkMath.ABC.RatioBound"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/--
`Keystone_eventual_ratio_bound` は、`MiddleBand_exception_bound` スタイルの境界から
`BadCount / X^2` の比の最終的な不等式を導出します。

## 引数
- `ε'` : 実数で、境界の調整に使用されます。
- `X0` : 自然数で、Xの下限を指定します。
- `C` : 実数で、境界の定数です。
- `hC` : `C` が0以上であることを示す証明。
- `hX` : 任意の自然数 `X` に対して、`X` が `X0` 以上のときに `BadCount` が指定された不等式を満たすことを示す証明。
- `hβ` : `1.75 + ε'` が2未満であることを示す証明。
- `hβ0` : `1.75 + ε'` が0以上であることを示す証明。

## 結果
- `∃ _ : ℕ, ∀ᶠ X in atTop, (BadCount (0.435) X : ℝ) / (X : ℝ) ^ 2 ≤ (C + 1) / (X : ℝ) ^ (2 - (1.75 + ε'))`
  という形で、最終的な不等式が存在することを示します。
-/
lemma Keystone_eventual_ratio_bound
  (ε' : ℝ) (X0 : ℕ) (C : ℝ) (hC : 0 ≤ C)
  (hX : ∀ X, X ≥ X0 → BadCount (0.435) X ≤ ⌈C * (X : ℝ) ^ (1.75 + ε')⌉₊)
  (hβ : 1.75 + ε' < 2) (hβ0 : 0 ≤ 1.75 + ε') :
  ∃ _ : ℕ, ∀ᶠ X in atTop, (BadCount (0.435) X : ℝ) / (X : ℝ) ^ 2 ≤ (C + 1) / (X : ℝ) ^ (2 - (1.75 + ε')) := by
  let X1 := max X0 1
  use X1
  apply Filter.eventually_atTop.2
  refine ⟨X1, by
    intro X hX1
    have hX_ge_X0 : X ≥ X0 := le_trans (le_max_left X0 1) hX1
    have hnat := hX X hX_ge_X0
    have hcast : (BadCount (0.435) X : ℝ) ≤ ↑(⌈C * (X : ℝ) ^ (1.75 + ε')⌉₊) := by exact_mod_cast hnat
    have hceil : (↑(⌈C * (X : ℝ) ^ (1.75 + ε')⌉₊) : ℝ) ≤ C * (X : ℝ) ^ (1.75 + ε') + 1 := by
      let y := C * (X : ℝ) ^ (1.75 + ε')
      have hy : 0 ≤ y := by
        have hCX : 0 ≤ C * (X : ℝ) ^ (1.75 + ε') := by
          apply mul_nonneg
          · linarith [hC]
          · apply Real.rpow_nonneg
            exact_mod_cast (Nat.zero_le X)
        exact hCX
      have hspec := Nat.ceil_spec y hy
      have hlt : (Nat.ceil y - 1 : ℝ) < y := by exact_mod_cast hspec.1
      have hle : (Nat.ceil y - 1 : ℝ) ≤ y := le_of_lt hlt
      calc
        (↑(Nat.ceil y) : ℝ) = (Nat.ceil y - 1 : ℝ) + 1 := by simp
        _ ≤ y + 1 := by linarith
    have hUp : (BadCount (0.435) X : ℝ) ≤ C * (X : ℝ) ^ (1.75 + ε') + 1 := by linarith
    have hX1' : 1 ≤ X := le_trans (le_max_right X0 1) hX1
    exact ratio_bound_of_poly_upper hβ hβ0 (by linarith [hC]) hX1' hUp
  ⟩

/-- 中帯の外部結果（強化版）： -/
axiom MiddleBand_exception_bound
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, X ≥ X0 →
      BadCount (0.435) X ≤ ⌈C * (X : ℝ) ^ (1.75 + ε)⌉₊

/--
密度 0（割合→0）：BadCount / X^2 ⟶ 0

`Keystone_density_zero_fraction` は、与えられた正の実数 `ε` に対して、
`BadCount` 関数を用いて、自然数 `X` に対する比率が `0` に収束することを示す定理です。
この定理は、`Tendsto` を使用して、`atTop` における収束を `nhds 0` に対して証明します。

## 引数
- `ε` : 正の実数。
- `hε` : `ε` が正であることを示す証明。

## 目的
- `BadCount (0.435) X` を `X^2` で割った値が、`X` が無限大に近づくときに `0` に収束することを示します。
- この定理は、密度の性質に関連する重要な結果であり、確率論や統計学における収束の概念に応用されます。
- 収束の証明は、実数の解析における基本的なテクニックを用いて行われ、数学的な証明や数理論理の文脈で重要な役割を果たします。
- この定理は、数学のさまざまな分野における研究の出発点となることが期待され、収束の性質を理解することは数学的な問題解決能力を向上させるために重要です。
-/
theorem Keystone_density_zero_fraction
  (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun X : ℕ => (BadCount (0.435) X : ℝ) / (X : ℝ) ^ 2) atTop (nhds 0) := by
  classical
  -- pick ε' = min ε 0.24 so 1.75 + ε' < 2
  let ε' := min ε (0.24 : ℝ)
  have hε' : 0 < ε' := by
    have h024 : 0 < (0.24 : ℝ) := by norm_num
    exact lt_min hε h024
  obtain ⟨X0, C, hC, hX⟩ := MiddleBand_exception_bound (ε := ε') hε'
  have hε'_lt : ε' < 0.25 := by
    simp only [ε']
    apply min_lt_iff.2
    right
    norm_num
  have hβ : (1.75 + ε') < 2 := by
    calc
      1.75 + ε' < 1.75 + 0.25 := add_lt_add_right hε'_lt 1.75
      _ = 2 := by norm_num
  have hβ0 : 0 ≤ 1.75 + ε' := by linarith
  let X1 := max X0 1
  let a := (2 - (1.75 + ε'))
  have alpha_pos : 0 < a := by
    -- a = 0.25 - ε' and ε' < 0.25, so a > 0
    dsimp [a]
    linarith [hε'_lt]
  -- Elementary fact: for a > 0, (X : ℝ) ^ a → ∞ as X → ∞.
  -- Use the existing lemma for positive exponents.
  -- (C + 1) / X^a = (C + 1) * (1 / X^a). ここで Real.tendsto_rpow_atTop を使わずに
  -- ε-議論で 1 / (X:ℝ)^a → 0 を直接示す。
  have hrecip : Tendsto (fun X : ℕ => (1 : ℝ) / (X : ℝ) ^ a) atTop (nhds 0) := by
    -- 定義から: 任意の ε > 0 に対して、十分大きな X で |1 / X^a - 0| < ε を示す
    intro eps heps
    -- 近傍 eps ∈ nhds 0 から正の実数 ε を取り出す
    obtain ⟨ε, hε_pos, hε_mem⟩ := Metric.mem_nhds_iff.1 heps
    have hepspos : 0 < ε := hε_pos
    -- (1 / ε)^(1/a) を境界とする：X > (1/ε)^(1/a) ならば 1 / X^a < ε
    let M := (1 / ε) ^ (1 / a)
    have hM_pos : 0 < M := by
      apply Real.rpow_pos_of_pos
      apply div_pos (by norm_num : (0 : ℝ) < 1) hepspos
    let N := (Nat.ceil M) + 1
    refine (Filter.eventually_atTop.2 ⟨N, by
      intro X hXge
      have hX_real : (X : ℝ) ≥ (N : ℝ) := by exact_mod_cast hXge
      have hN_gt_ceil : (N : ℝ) > (Nat.ceil M : ℝ) := by
        exact_mod_cast Nat.lt_add_one (Nat.ceil M)
      have hceil_ge_M : (Nat.ceil M : ℝ) ≥ M := by
        have hy : 0 ≤ M := by linarith [hM_pos]
        have hspec := Nat.ceil_spec M hy
        exact_mod_cast hspec.2
      have hX_gt_M : (X : ℝ) > M := by
        calc
          (X : ℝ) ≥ (N : ℝ) := hX_real
          _ > (Nat.ceil M : ℝ) := hN_gt_ceil
          _ ≥ M := hceil_ge_M
      -- X > M > 0 と a > 0 により (X:ℝ)^a > M^a = 1 / eps
      have hpow_gt : (X : ℝ) ^ a > M ^ a := by
        -- Real.rpow_lt_rpow を使う：0 < M < X, 0 < a
        apply Real.rpow_lt_rpow;
        { linarith [hM_pos, hX_gt_M] }
        { exact hX_gt_M }
        { exact alpha_pos }
      have hM_pow : M ^ a = (1 : ℝ) / ε := by
        dsimp [M]
        have hnonneg : 0 ≤ (1 : ℝ) / ε := div_nonneg (by norm_num) (le_of_lt hε_pos)
        -- ((1/ε)^(1/a))^a = (1/ε)^{(1/a)*a}
        rw [←Real.rpow_mul hnonneg]
        have ha : (1 / a) * a = 1 := by field_simp [ne_of_gt alpha_pos]
        rw [ha]
        simp only [one_div, rpow_one]
      -- From X^a > M^a = 1/ε we have 1 < ε * X^a, so by div_lt_iff
      -- 1 / X^a < ε holds. Then |1 / X^a - 0| < ε, hence membership of the ball.
      have h1 : (X : ℝ) ^ a > 1 / ε := by
        calc
          (X : ℝ) ^ a > M ^ a := hpow_gt
          _ = 1 / ε := by rw [hM_pow]
      have hmul : (1 : ℝ) < ε * (X : ℝ) ^ a := by
        calc
          1 = ε * (1 / ε) := by field_simp [ne_of_gt hε_pos]
          _ < ε * (X : ℝ) ^ a := mul_lt_mul_of_pos_left h1 hε_pos
      have hposXpow : 0 < (X : ℝ) ^ a := Real.rpow_pos_of_pos (lt_trans hM_pos hX_gt_M) a
      have hlt : (1 : ℝ) / (X : ℝ) ^ a < ε := (div_lt_iff (hc := hposXpow)).mpr hmul
      have hpos_inv : 0 < (1 : ℝ) / (X : ℝ) ^ a := div_pos (by norm_num : (0 : ℝ) < 1) hposXpow
      have h_mem_ball : abs (1 / (↑X : ℝ) ^ a - 0) < ε := by
        simp only [sub_zero]
        rwa [abs_of_pos hpos_inv]
      -- use the fact that Metric.ball 0 ε ⊆ eps to show membership and finish
      exact hε_mem h_mem_ball
    ⟩)

  -- combine bounds: use the eventual bound and the fact that (C+1)/X^a → 0
  have ⟨N, eventually_bound⟩ := Keystone_eventual_ratio_bound ε' X0 C hC hX hβ hβ0
  have hCpos : 0 < C + 1 := by linarith [hC]
  have hrhs := Filter.Tendsto.const_mul (C + 1) hrecip
  have hrhs0 : Tendsto (fun k : ℕ => (C + 1) * (1 / (↑k : ℝ) ^ a)) atTop (nhds 0) := by simpa [mul_zero] using hrhs
  -- show 0 ≤ (BadCount / k^2) eventually (trivial since numerator, denominator nonneg)
  have hpos_eventually : ∀ᶠ n in atTop, 0 ≤ (BadCount (0.435) n : ℝ) / (n : ℝ) ^ 2 := by
    filter_upwards [eventually_bound] with n hn
    have hnum_nonneg : 0 ≤ (BadCount (0.435) n : ℝ) := by exact_mod_cast Nat.zero_le (BadCount (0.435) n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ 2 := by apply pow_nonneg; exact_mod_cast Nat.zero_le n
    exact div_nonneg hnum_nonneg hden_nonneg
  -- show (BadCount / n^2) ≤ (C+1)/n^a eventually (it's `eventually_bound` itself, up to rewriting)
  have hupper_eventually : ∀ᶠ n in atTop, (BadCount (0.435) n : ℝ) / (n : ℝ) ^ 2 ≤ (C + 1) * (1 / (↑n : ℝ) ^ a) := by
    filter_upwards [eventually_bound] with n hn
    simpa [div_eq_mul_inv] using hn
  exact Filter.Tendsto.squeeze' (tendsto_const_nhds) hrhs0 hpos_eventually hupper_eventually
  -- exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) hrhs0 hpos_eventually hupper_eventually
  -- done

/- Convenience wrapper: for any positive η, eventually BadCount ≤ η * X^2 -/

/--
使いやすい形の補題：任意の正の η に対し、十分大きな X で
(BadCount X : ℝ) ≤ η * X^2 が成り立つことを与える（密度 0 からの直接的帰結）。

`eventually_badcount_le_eps'` は、与えられた正の実数 `η` に対して、上限において
`BadCount (0.435) X` が `η * (X : ℝ) ^ 2` 以下であることが成り立つことを示す補題です。
この補題は、特定の条件下での漸近的な挙動を扱います。

## 引数
- `η` : 正の実数。
- `hη` : `η` が正であることを示す仮定。

## 結果
- `∀ᶠ X in atTop` : `X` が無限大に近づくときの条件。
- `BadCount (0.435) X : ℝ` が `η * (X : ℝ) ^ 2` 以下であることを示します。
- この補題は、確率論や解析学における重要な結果を提供します。
- 使用する際は、`BadCount` の定義とその性質を理解していることが前提です。
- 具体的な応用例や関連する理論については、追加の文献を参照してください。
- この補題は、数学的な証明や解析において重要な役割を果たします。
- 例として、確率分布の収束や大数の法則に関連する問題に適用可能です。
- さらなる詳細は、関連する文献や資料を参照してください。
- この補題は、数学的な議論や研究において有用です。
- 具体的な使用例や応用については、他の文献を参照してください。
-/
lemma eventually_badcount_le_eps' {η : ℝ} (hη : 0 < η) :
  ∀ᶠ X in atTop, (BadCount (0.435) X : ℝ) ≤ η * (X : ℝ) ^ 2 := by
  -- From the proven tendsto of BadCount/X^2 to 0 we get an eventual smallness
  have h := Keystone_density_zero_fraction η hη
  -- Convert tendsto to an eventual statement by applying it to the ball around 0
  let s := Metric.ball (0 : ℝ) η
  have s_mem : s ∈ nhds (0 : ℝ) := by
    apply Metric.mem_nhds_iff.2
    use η
  -- convert tendsto f atTop (nhds 0) to: ∀ᶠ n in atTop, f n ∈ s
  have hsmall := h s_mem
  -- also ensure X ≥ 1 eventually so denominators are nonzero
  have ev1 := Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩
  filter_upwards [hsmall, ev1] with n hn_small hn_ge1
  -- dist(x, 0) = |x - 0| = |x| なので、絶対値に書き換えるのじゃ。
  have hraw : (BadCount (0.435) n : ℝ) / (n : ℝ) ^ 2 < η := by
    simpa [dist_zero_right] using Metric.mem_ball.mp hn_small
  -- numerator and denominator are nonnegative, so we can replace abs by value
  have hnum_nonneg : 0 ≤ (BadCount (0.435) n : ℝ) := by exact_mod_cast Nat.zero_le (BadCount (0.435) n)
  have hden_nonneg : 0 ≤ (n : ℝ) ^ 2 := by apply pow_nonneg; exact_mod_cast Nat.zero_le n
  have hfrac_nonneg := div_nonneg hnum_nonneg hden_nonneg
  have habs : |(BadCount (0.435) n : ℝ) / (n : ℝ) ^ 2| < η := by
    rw [abs_of_nonneg hfrac_nonneg]
    exact hraw
  -- now habs is (BadCount n)/n^2 < η; multiply both sides by n^2 (>0) to get the desired bound
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn_ge1)
  have hden_pos : 0 < (n : ℝ) ^ 2 := pow_pos hpos 2
  have hlt := mul_lt_mul_of_pos_right hraw hden_pos
  have hden_ne : (n : ℝ) ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hleft : (BadCount (0.435) n : ℝ) = ((BadCount (0.435) n : ℝ) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
    field_simp [hden_ne]
  have hfinal : (BadCount (0.435) n : ℝ) < η * (n : ℝ) ^ 2 := by
    rw [hleft]
    -- hlt : (BadCount n / n^2) * n^2 < η * n^2
    -- n^2 > 0 より両辺を n^2 で割っても不等式は保たれる
    exact hlt
  exact le_of_lt hfinal

/-- Markov 型の粗い上界：
与えられた閾値 η>0 に対して、スライスごとに `sliceBadCount δ X b ≥ η * X` を満たす b の個数を
全体の BadCount で抑える不等式を与える補題。具体的にはその個数を `BadCount / (η X)` の上界で抑える。
この補題は slice_sum_le_badcount と組み合わせて、平均化・Markov の議論に用いる。 -/
lemma slice_markov_card_le {δ η : ℝ} (_ : 0 < η) (X : ℕ) :
  (((Finset.range (X+1)).filter fun b => (sliceBadCount δ X b : ℝ) ≥ η * (X : ℝ)).card : ℝ)
    * (η * (X : ℝ)) ≤ (BadCount δ X : ℝ) := by
  -- define S as the filter of b with large sliceBadCount
  let S := (Finset.range (X+1)).filter fun b => (sliceBadCount δ X b : ℝ) ≥ η * (X : ℝ)
  -- const-sum = card * const
  have hconst : (∑ b ∈ S, η * (X : ℝ)) = (S.card : ℝ) * (η * (X : ℝ)) := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul, mul_comm]
  -- for b ∈ S we have η*X ≤ sliceBadCount (coerced to ℝ)
  have hterm_le : ∀ b ∈ S, η * (X : ℝ) ≤ (sliceBadCount δ X b : ℝ) := by
    intro b hb
    rcases Finset.mem_filter.1 hb with ⟨_hbR, hbP⟩
    exact hbP
  -- therefore sum over S of η*X ≤ sum over S of sliceBadCount (as ℝ)
  have hsumS_le : (∑ b ∈ S, η * (X : ℝ)) ≤ (∑ b ∈ S, (sliceBadCount δ X b : ℝ)) := by
    apply Finset.sum_le_sum
    intro b hb
    exact hterm_le b hb
  -- sum over S is ≤ sum over all b ∈ range (nonnegativity gives monotonicity)
  have hsubset : S ⊆ Finset.range (X+1) := Finset.filter_subset _ _
  have hnonneg : ∀ b ∈ Finset.range (X+1), 0 ≤ (sliceBadCount δ X b : ℝ) := by
    intro b hb; exact_mod_cast Nat.zero_le (sliceBadCount δ X b)
  -- sum over S ≤ sum over all b ∈ range because S ⊆ range
  have hsum_all_ge : (∑ b ∈ S, (sliceBadCount δ X b : ℝ)) ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b hb _ => hnonneg b hb)
  -- combine inequalities: (S.card)*η*X = sum_const ≤ sum_S ≤ sum_all ≤ BadCount
  calc
    (S.card : ℝ) * (η * (X : ℝ)) = (∑ b ∈ S, η * (X : ℝ)) := by rw [hconst]
    _ ≤ (∑ b ∈ S, (sliceBadCount δ X b : ℝ)) := hsumS_le
    _ ≤ (∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℝ)) := hsum_all_ge
    _ ≤ (BadCount δ X : ℝ) := by
      have hnat := slice_sum_le_badcount δ X
      exact_mod_cast hnat

-- -------------------------------------------------------

/--
密度1の運用形：任意 η>0 で十分大の X 以降、BadCount ≤ η·X^2
「密度1（割合→0）の運用形」

定理 `eventually_badcount_le_eps` は、特定の条件下で `BadCount` 関数が
与えられた `η` の値に対して上限を持つことを示します。

引数:
- `δ` : 実数で、特定の値（ここでは 0.435）に設定されます。
- `hδ` : `δ` が 0.435 であることを示す証明。
- `η` : 正の実数で、上限の計算に使用されます。
- `hη` : `η` が 0 より大きいことを示す証明。

結果:
- `X` が無限大に近づくとき、`BadCount δ X` は `η * (X : ℝ) ^ 2` 以下であることが
  成り立つことを示します。
-/
theorem eventually_badcount_le_eps
  {δ : ℝ} (hδ : δ = 0.435)
  (η : ℝ) (hη : 0 < η) :
  ∀ᶠ X in atTop, (BadCount δ X : ℝ) ≤ η * (X : ℝ) ^ 2 := by
  -- 割合→0 から |…| < η を取り、分母が正の範囲で掛け戻すだけ
  have h0 := Keystone_density_zero_fraction (ε := η/2) (by linarith)
  have hlt0 := (tendsto_order.1 h0).2 _ hη
  -- transport the eventual statement from BadCount 0.435 to BadCount δ using hδ
  have hlt : ∀ᶠ X in atTop, (BadCount δ X : ℝ) / (X : ℝ) ^ 2 < η := by
    filter_upwards [hlt0] with X h using by
      simpa [hδ.symm] using h
  -- さらに X ≥ 1 を同時に仮定できるようにして、分母が 0 にならぬことを保証するのじゃ。
  let ev1 := Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩
  have hboth := hlt.and ev1
  exact hboth.mono (by
    intro X ⟨hx, hge1⟩
    -- X ≥ 1 より (X:ℝ)^2 > 0 が分かる
    have hxpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hge1)
    have hxpos2 : 0 < (X : ℝ) ^ 2 := pow_pos hxpos 2
    -- (BadCount / X^2) < η を両辺に X^2 (>0) を掛けて変形する
    have hmul := mul_lt_mul_of_pos_right hx hxpos2
    have hden_ne : (X : ℝ) ^ 2 ≠ 0 := ne_of_gt hxpos2
    have hleft : ((BadCount δ X : ℝ) / (X : ℝ) ^ 2) * (X : ℝ) ^ 2 = (BadCount δ X : ℝ) := by
      field_simp [hden_ne]
    have hfinal : (BadCount δ X : ℝ) < η * (X : ℝ) ^ 2 := by
      simpa [hleft] using hmul
    exact le_of_lt hfinal)

/--
eventually から「∃X0, ∀X≥X0, …」へ

この定理 `exists_X0_badcount_le_eps` は、特定の条件の下で存在する自然数 `X0` を示します。
具体的には、与えられた実数 `δ` が 0.435 に等しく、実数 `η` が正である場合に、
任意の自然数 `X` が `X0` 以上であるとき、`BadCount δ X` が `η * X^2` 以下であることを保証します。

## 引数
- `δ` : 実数で、特定の値 0.435 に設定されます。
- `η` : 正の実数。
- `hδ` : `δ` が 0.435 であることを示す証明。
- `hη` : `η` が正であることを示す証明。

## 結果
- 自然数 `X0` が存在し、すべての `X` が `X0` 以上であるとき、`BadCount δ X` が `η * X^2` 以下であることが成り立ちます。
-/
theorem exists_X0_badcount_le_eps
  {δ : ℝ} (hδ : δ = 0.435) (η : ℝ) (hη : 0 < η) :
  ∃ X0 : ℕ, ∀ X ≥ X0, (BadCount δ X : ℝ) ≤ η * (X : ℝ) ^ 2 := by
  have h := eventually_badcount_le_eps (δ:=δ) (hδ:=hδ) (η:=η) hη
  have ⟨s, hs_mem, hs_forall⟩ := (Filter.eventually_iff_exists_mem.1 h)
  -- s ∈ atTop なら、∃ X0, Ici X0 ⊆ s が成り立つ（atTop の定義より）
  have ⟨X0, hIci⟩ : ∃ X0, Set.Ici X0 ⊆ s :=
    by simpa using hs_mem
  exact ⟨X0, fun X h => hs_forall X (hIci h)⟩

/- 要石の密度1版： δ=0.435 が“例外集合を除き”成立する。 -/

/- ### 補助：実数天井の吸収（既に Utils にある系を使って短く） -/

/-- `↑⌈y⌉₊ ≤ y + 1` （`Nat.ceil_spec` と `Int.ceil_le_add_one` から従う） -/
@[simp]
lemma natCeil_le_add_one_real {y : ℝ} (hy : 0 ≤ y) :
  (↑(⌈y⌉₊) : ℝ) ≤ y + 1 := by
  -- Nat.ceil_spec より ↑(⌈y⌉₊) < y + 1 が得られるのでこれを用いる
  have h := Nat.ceil_spec y hy
  -- Nat.ceil_spec より ↑⌈y⌉₊ - 1 < y なので、↑⌈y⌉₊ < y + 1 が従う
  linarith [h.left]

/- ### 抽出補題：有用な中間事実を定理化する -/

/-- 定義 M := ((|K|)/eps)^(1/α) に対して M^α = |K|/eps である（α>0, eps>0, K≠0 を仮定） -/
private lemma M_pow_alpha_eq (K eps α : ℝ) (hα : 0 < α) (heps : 0 < eps) (hK_ne : K ≠ 0) :
  (((abs K) / eps) ^ (1 / α)) ^ α = |K| / eps := by
  have habs_pos : 0 < |K| := abs_pos.mpr hK_ne
  have hpos : 0 < (abs K) / eps := div_pos habs_pos heps
  calc
    (((abs K) / eps) ^ (1 / α)) ^ α = ((abs K) / eps) ^ ((1 / α) * α) := by
      -- 基底が正であること hpos を明示して乗法則を使う
      rw [← Real.rpow_mul (le_of_lt hpos)]
    _ = ((abs K) / eps) ^ 1 := by
      have hmul : (1 / α) * α = 1 := by field_simp [hα.ne']
      rw [hmul]
      simp
    _ = |K| / eps := by
      simp

/- 1 を下界にもつ N の定義に関する自明補題 -/

/-- 定義 N := (⌈M⌉₊ : ℕ) + 1 は常に 1 以上である -/
private lemma N_ge_one (M : ℝ) : 1 ≤ ((⌈M⌉₊ : ℕ) + 1) := by
  have hceil_nonneg : 0 ≤ ⌈M⌉₊ := Nat.zero_le _
  calc
    1 = 0 + 1 := by rfl
    _ ≤ ⌈M⌉₊ + 1 := by exact Nat.add_le_add_right hceil_nonneg 1

/-- `n ≤ ⌈t⌉₊` かつ `0 ≤ t` のとき `(n : ℝ) ≤ t + 1` -/
private lemma le_cast_ceil_add_one {n : ℕ} {t : ℝ} (h : n ≤ ⌈t⌉₊) (ht : 0 ≤ t) :
  (n : ℝ) ≤ t + 1 := by
  have hceil := natCeil_le_add_one_real ht
  have : (n : ℝ) ≤ (↑(⌈t⌉₊) : ℝ) := by exact_mod_cast h
  linarith [this, hceil]

/-- `0 ≤ M` のとき `↑⌈M⌉₊ + 1 > M` -/
private lemma ceil_add_one_gt_of_nonneg {M : ℝ} (hM : 0 ≤ M) :
  ((⌈M⌉₊ : ℕ) + 1 : ℝ) > M := by
  have h := Nat.ceil_spec M hM
  linarith [h.left]

/-- 自然数 X ≥ 1 のとき (X : ℝ) > 0 -/
private lemma nat_cast_pos_of_ge1 (X : ℕ) (hXge1 : X ≥ 1) : 0 < (X : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hXge1))

/-- 自然数を実数へキャストすると非負になる -/
private lemma nat_cast_nonneg (n : ℕ) : 0 ≤ (n : ℝ) := by
  exact_mod_cast Nat.zero_le n

/-- 単純な rad クラスのカウント補題：固定 r に対して a ≤ X かつ rad a = r を満たす a の個数は
    r が 0 でない限り最大で ⌊X / r⌋ + 1 に抑えられる。
    証明は rad a = r のとき r ∣ a であることに基づき、r の倍数の個数を数えるだけじゃ。
-/
lemma count_with_rad_eq_le_div (r X : ℕ) (hr : r ≠ 0) :
  ((Finset.range (X+1)).filter fun a => a ≤ X ∧ rad a = r).card ≤ (X / r) + 1 := by
  let S := (Finset.range (X+1)).filter fun a => a ≤ X ∧ rad a = r
  let M := (Finset.range (X+1)).filter fun a => r ∣ a

  -- S ⊆ M because rad a = r implies r ∣ a (handle a = 0 separately)
  have S_sub_M : S ⊆ M := by
    intro a ha
    rcases Finset.mem_filter.1 ha with ⟨haR, haP⟩
    rcases haP with ⟨_ha_le, ha_rad⟩
    by_cases ha0 : a = 0
    · -- a = 0 の場合は自明
      subst ha0
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.zero_lt_succ X), dvd_zero r⟩
    · -- a ≠ 0 の場合は factorization を使って rad a ∣ a を示す
      have hn0 : a ≠ 0 := ha0
      let f := a.factorization
      let s := f.support
      have hfac : a = s.prod (fun p => p ^ f p) := Eq.symm (Nat.factorization_prod_pow_eq_self hn0)
      have hdiv : s.prod (fun p => p) ∣ s.prod (fun p => p ^ f p) := by
        apply Finset.prod_dvd_prod_of_dvd
        intro p hp
        have hf : f p ≠ 0 := by simpa using (Finsupp.mem_support_iff.mp hp)
        exact dvd_pow_self p hf
      have hrad_dvd_a : s.prod (fun p => p) ∣ a := by
        rw [hfac]
        exact hdiv
      have : r ∣ a := by
        rw [← ha_rad]
        exact hrad_dvd_a
      exact Finset.mem_filter.2 ⟨haR, this⟩

  -- Each element of M is r*k for some k ≤ X / r, so M ⊆ image(range (X / r + 1))
  have M_sub_img : M ⊆ (Finset.range (X / r + 1)).image (fun k => r * k) := by
    intro a ha
    rcases Finset.mem_filter.1 ha with ⟨haR, haDvd⟩
    have a_le : a ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp haR)
    rcases haDvd with ⟨k, rfl⟩
    have hk_le : k ≤ X / r := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hr)).mpr (by simpa [Nat.mul_comm] using a_le)
    have hk_in : k ∈ Finset.range (X / r + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)
    exact Finset.mem_image.2 ⟨k, hk_in, rfl⟩

  -- image(range (X / r + 1)) has cardinality (X / r) + 1 because k ↦ r*k is injective
  have card_img : ((Finset.range (X / r + 1)).image (fun k => r * k)).card = (X / r) + 1 := by
    calc
      ((Finset.range (X / r + 1)).image (fun k => r * k)).card
        = (Finset.range (X / r + 1)).card := Finset.card_image_of_injective _ (by
          intro x y h; exact (Nat.mul_left_inj hr).1 (by simpa [Nat.mul_comm] using h))
      _ = (X / r) + 1 := by simp

  -- combine the subset relations to get the desired upper bound
  have hS_le : S.card ≤ M.card := Finset.card_le_card S_sub_M
  have hM_le_img : M.card ≤ ((Finset.range (X / r + 1)).image (fun k => r * k)).card := Finset.card_le_card M_sub_img
  calc
    S.card ≤ M.card := hS_le
    _ ≤ ((Finset.range (X / r + 1)).image (fun k => r * k)).card := hM_le_img
    _ = (X / r) + 1 := by rw [card_img]

/-- `0 ≤ M` のとき `M ≤ ↑⌈M⌉₊` を取り出す補題 -/
private lemma ceil_ge_nonneg (M : ℝ) (hM : 0 ≤ M) : M ≤ (↑⌈M⌉₊ : ℝ) :=
  (Nat.ceil_spec M hM).right

/-- `0 < M` のとき `0 < ⌈M⌉₊` を取り出す補題 -/
private lemma ceil_pos_of_pos (M : ℝ) (hM : 0 < M) : 0 < ⌈M⌉₊ := by
  -- もし ⌈M⌉₊ = 0 ならば (⌈M⌉₊ : ℝ) = 0 だから M ≤ 0 になり矛盾する
  have hceil_ne0 : ⌈M⌉₊ ≠ 0 := by
    intro heq
    have : (⌈M⌉₊ : ℝ) = 0 := by simp [heq]
    have hle := (Nat.ceil_spec M (le_of_lt hM)).right
    linarith [hle, this]
  exact Nat.pos_of_ne_zero hceil_ne0

/-- 自然数 X ≥ 1 と α>0 のとき (X : ℝ)^α > 0 -/
private lemma nat_rpow_pos_of_ge1 (X : ℕ) (hXge1 : X ≥ 1) (α : ℝ) : 0 < (X : ℝ) ^ α := by
  apply Real.rpow_pos_of_pos
  exact nat_cast_pos_of_ge1 X hXge1

/- 更に小さな補題群：Nat の不等号を実数キャストへ移す等 -/

/-- 自然数の不等号を実数にキャストする：X ≥ N なら (X : ℝ) ≥ (N : ℝ) -/
private lemma cast_nat_ge_of_ge (X N : ℕ) (h : X ≥ N) : (X : ℝ) ≥ (N : ℝ) := by
  exact_mod_cast h

/-- N の実数表現が M より大きく、X ≥ N のとき (X : ℝ) > M が成り立つ -/
private lemma cast_nat_gt_of_ge_and_gt (X N : ℕ) (M : ℝ) (hN_gt_M : (N : ℝ) > M) (hXgeN : X ≥ N) :
  (X : ℝ) > M := by
  have : (X : ℝ) ≥ (N : ℝ) := by exact_mod_cast hXgeN
  exact lt_of_lt_of_le hN_gt_M this

/-- 分母が正のときノルムを絶対値と分数に展開する補題 -/
private lemma norm_div_by_pos {a b : ℝ} (hb : 0 < b) : ‖a / b‖ = |a| / b := by
  calc
    ‖a / b‖ = |a / b| := by rw [Real.norm_eq_abs]
    _ = |a| / |b| := by rw [abs_div]
    _ = |a| / b := by rw [abs_of_pos hb]

/- 小さな利用可能補題：与えた定義の N 以上なら分数は小さくできる、という補題（証明は元の証明を簡潔化） -/
/-- 単純化された補題：α>0, eps>0, K≠0 として
  N := ⌈((|K|)/eps)^(1/α)⌉₊ + 1 と取れば任意の X ≥ N に対して |K / X^α| < eps が成り立つ -/
lemma abs_div_lt_for_large_nat (α K eps : ℝ) (hα : 0 < α) (heps : 0 < eps) (hK_ne : K ≠ 0)
  (X : ℕ) (hXge : X ≥ ((⌈((abs K) / eps) ^ (1 / α)⌉₊ : ℕ) + 1)) :
  |K / (X : ℝ) ^ α| < eps := by
  -- 基底が正であること
  have hbase_pos : 0 < (abs K) / eps := div_pos (abs_pos.mpr hK_ne) heps
  let M := (abs K / eps) ^ (1 / α)
  have hM_pos : 0 < M := Real.rpow_pos_of_pos hbase_pos (1 / α)
  -- N := ⌈M⌉ + 1 が M より大きいこと
  have hN_gt_M : (↑((⌈M⌉₊ : ℕ) + 1) : ℝ) > M := by
    have hceil := Nat.ceil_spec M (le_of_lt hM_pos)
    calc
      ↑((⌈M⌉₊ : ℕ) + 1) = (↑(⌈M⌉₊ : ℕ) : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
      _ > M := by
        apply lt_add_of_le_of_pos
        · exact hceil.right
        · norm_num
  -- X ≥ N から (X : ℝ) > M
  have hX_ge_N : (X : ℝ) ≥ (↑((⌈M⌉₊ : ℕ) + 1) : ℝ) := by exact_mod_cast hXge
  have hX_gt_M : (X : ℝ) > M := lt_of_lt_of_le hN_gt_M hX_ge_N
  -- よってべき乗で比較して (X^α) > M^α
  have hM_pow_pos : 0 < M := hM_pos
  have hpow_gt : (X : ℝ) ^ α > M ^ α := by
    have htmp : M ^ α < (X : ℝ) ^ α :=
      Real.rpow_lt_rpow (le_of_lt hM_pos) hX_gt_M hα
    exact htmp
  -- M^α = |K| / eps による置換
  have hM_pow_eq := M_pow_alpha_eq K eps α hα heps hK_ne
  have h_gt : (X : ℝ) ^ α > |K| / eps := by
    calc
      (X : ℝ) ^ α > M ^ α := hpow_gt
      _ = |K| / eps := by rw [hM_pow_eq]
  -- 両辺に eps(>0) を掛けて整理すると |K|/(X^α) < eps が得られる
  have hpos_denom : 0 < (X : ℝ) ^ α :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le hM_pos (le_of_lt hX_gt_M)) α
  have h_mul : eps * (X : ℝ) ^ α > |K| := by
    calc
      eps * (X : ℝ) ^ α > eps * (|K| * eps⁻¹) := by
        apply mul_lt_mul_of_pos_left h_gt heps
      _ = |K| := by
        field_simp [heps.ne']
  -- eps * X^α > |K| から |K| / X^α < eps を得る
  have hdiv : |K| / (X : ℝ) ^ α < eps := (div_lt_iff hpos_denom).mpr h_mul
  -- 分母が正なので絶対値を分けて結論を得る
  calc
    |K / (X : ℝ) ^ α| = |K| / (X : ℝ) ^ α := by
      rw [abs_div, abs_of_pos hpos_denom]
    _ < eps := hdiv

end ABC
