/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC037

#print "file: DkMath.ABC.ABC038"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ABC予想では a + b = c の a, b, c は 0 < a, 0 < b, 0 < c とすることが多いが、
-- ここでは自然数全体で定義しているので、0 を含む場合も考慮する必要がある。
-- ただし、Bad_ε c γ_values の否定を仮定しているので、c = 0 の場合は排除される。
-- よって c ≥ 1 として議論を進めることができる。
lemma abc_c_pos {a b c : ℕ} (hrel : a + b = c)
    (hcoprime : IsCoprime a b)
    (γ_values : ℕ → ℝ)
    (_hnb : ¬Bad_ε c γ_values) :
    1 ≤ c := by
  by_contra h
  -- ¬(1 ≤ c) implies c = 0 for natural numbers
  have hc0 : c = 0 := by
    cases c with
    | zero =>
        rfl
    | succ c' =>
        -- In this case we have 1 ≤ succ c', contradicting h : ¬ (1 ≤ c)
        have : 1 ≤ Nat.succ c' := by
          exact Nat.succ_le_succ (Nat.zero_le _)
        exact False.elim (h this)
  have hab0 : a = 0 ∧ b = 0 := by
    rw [hc0] at hrel
    exact Nat.add_eq_zero_iff.mp hrel
  rcases hab0 with ⟨ha0, hb0⟩
  have hcoprime_false : ¬ IsCoprime a b := by
    rw [ha0, hb0]
    exact not_isCoprime_zero_zero
  contradiction


lemma not_isCoprime_zero_nonzero {n : ℕ} (hn : 1 < n) : ¬ IsCoprime 0 n := by
  -- If n > 1, there are no a,b with a*0 + b*n = 1.
  intro hcop
  rcases hcop with ⟨u, v, h_be_z_out⟩
  -- u * 0 + v * n = 1 so v * n = 1
  have hvn : v * n = 1 := by
    rw [mul_zero, zero_add] at h_be_z_out
    exact h_be_z_out
  -- From v * n = 1 we get n ∣ 1, hence n = 1, contradicting 1 < n
  have hdvd : n ∣ 1 := by
    use v
    rw [mul_comm] at hvn
    exact hvn.symm
  -- from 1 ≤ n and n = 1 we get a contradiction with 1 ≤ n when originally assuming strict >1
  have hn1 : n = 1 := Nat.eq_one_of_dvd_one hdvd
  rw [hn1] at hn
  linarith

lemma not_isCoprime_nonzero_zero {n : ℕ} (hn : 1 < n) : ¬ IsCoprime n 0 := by
  -- If n > 1, there are no a,b with a*n + b*0 = 1.
  intro hcop
  rcases hcop with ⟨u, v, h_be_z_out⟩
  -- u * n + v * 0 = 1 so u * n = 1
  have hun : u * n = 1 := by
    rw [mul_zero, add_zero] at h_be_z_out
    exact h_be_z_out
  -- From u * n = 1 we get n ∣ 1, hence n = 1, contradicting 1 < n
  have hdvd : n ∣ 1 := by
    use u
    -- rewrite to n * u = 1 to match divisor witness shape
    rw [mul_comm] at hun
    exact hun.symm
  have hn1 : n = 1 := Nat.eq_one_of_dvd_one hdvd
  rw [hn1] at hn
  linarith

-- `n` の素因子リスト `Nat.factors n` に含まれるなら素数である、という補題
lemma prime_of_mem_factorization_support {n p : ℕ} (hp : p ∈ (Nat.factorization n).support) : Nat.Prime p := by
  -- `mem_support_factorization_iff` は `p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n)` を与える
  have h : n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n := by
    rwa [ABC.mem_support_factorization_iff] at hp
  exact h.2.1

-- ==========================================
-- Bad_ε_ABC: ABC予想の品質評価用の定義
-- ==========================================

/-- 【設計ノート：Bad_ε vs Bad_ε_ABC】

このファイルには2つの「悪い」条件の定義が存在する：

1. Bad_ε (Chernoff バウンド用)
   - 定義：Bad_ε n γ_values := ∃ p ≥ 3, p.Prime ∧ Excess p (γ_values p) n
   - Excess の意味：((Vp p n : ℤ) : ℝ) - 2 > γ
   - Vp の定義：Vp p n := padicValNat p (2*n+1)
   - 用途：連続する奇数 2n+1 の列に対する密度評価
   - 設計理由：Chernoff バウンドで「n ∈ [0, X] のうち何個が bad か」を評価

2. Bad_ε_ABC (ABC 品質不等式用)
   - 定義：Bad_ε_ABC c γ_values := ∃ p ≥ 3, p.Prime ∧ Excess_ABC p (γ_values p) c
   - Excess_ABC の意味：((padicValNat p c : ℤ) : ℝ) - 2 > γ
   - 用途：c 自体の素因数分解に基づく品質評価
   - 設計理由：twoTail c の定義が c.factorization を使うため

【重要な相違点】
- Vp p n = padicValNat p (2*n+1) ... 奇数列の評価
- padicValNat p c ................ c 自体の評価

これらは一般に異なる値を持つ：
  例：c = 4 のとき
  - padicValNat 2 4 = 2
  - padicValNat 2 (2*4+1) = padicValNat 2 9 = 0

【現状の実装状況】

完成済み（sorry なし）：
- quality_le_of_not_bad_with_tail: π + TailBound → quality の核心ブリッジ
- tailbound_of_log_bound: ログ境界 → TailBound の変換
- quality_le_of_not_bad_with_log: ¬Bad + ログ境界 → quality の便利版

未完成（sorry あり）：
- quality_le_of_not_bad: Bad_ε を使う版（設計上の問題で実装困難）
- quality_le_of_not_bad_abc: Bad_ε_ABC を使う版（将来実装予定）
- twoTail_log_bound_of_not_bad_eps: Bad_ε → ログ境界（設計上の問題）
- twoTail_log_bound_of_not_bad_eps_budget: 予算版（ステップ2に問題）

【推奨される使用方法】

現時点では以下のワークフローを推奨：
1. Bad_ε_ABC を使って品質不等式を証明する
2. または、quality_le_of_not_bad_with_tail/with_log を直接使う
3. TailBound や ログ境界を別の方法で確保する

【将来の改善案】

選択肢A: Bad_ε の定義を変更
  - Vp p n := padicValNat p n に変更
  - メリット：統一的な定義、実装がシンプル
  - デメリット：Chernoff 側の証明を全面的に見直す必要がある

選択肢B: Bad_ε_ABC を主軸にする
  - 品質不等式は Bad_ε_ABC ベースで実装
  - Bad_ε は密度評価専用として残す
  - メリット：既存の証明に影響しない、役割が明確
  - デメリット：2つの定義を維持する必要がある

選択肢C: 橋渡し補題を追加
  - padicValNat p (2*c+1) と padicValNat p c の関係を示す
  - メリット：両方の定義を活かせる
  - デメリット：一般的な関係式が存在しない（場合分けが複雑）

現時点では選択肢B（Bad_ε_ABC を主軸）が最も現実的と判断される。
-/

-- ABC予想の文脈では、c 自体の p-adic valuation を使う
def Excess_ABC (p : ℕ) (γ : ℝ) (c : ℕ) : Prop :=
  ((padicValNat p c : ℤ) : ℝ) - 2 > γ

def Bad_ε_ABC (c : ℕ) (γ_values : ℕ → ℝ) : Prop :=
  ∃ p ≥ 3, p.Prime ∧ Excess_ABC p (γ_values p) c

-- 補助補題：¬Bad_ε_ABC から各素数 p に対する制約を抽出
lemma not_bad_abc_implies_vp_bound {c : ℕ} {γ_values : ℕ → ℝ}
    (h : ¬Bad_ε_ABC c γ_values) :
    ∀ p ≥ 3, p.Prime → ((padicValNat p c : ℤ) : ℝ) ≤ γ_values p + 2 := by
  intro p hp3 hprime
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : γ_values p + 2 < ((padicValNat p c : ℤ) : ℝ)
  have h_excess : Excess_ABC p (γ_values p) c := by
    unfold Excess_ABC
    linarith
  have h_bad : Bad_ε_ABC c γ_values := by
    unfold Bad_ε_ABC
    exact ⟨p, hp3, hprime, h_excess⟩
  exact h h_bad

-- twoTail の対数バウンドを導く補題
lemma twoTail_log_bound_of_not_bad_abc
    {a b c : ℕ} (hc : c ≠ 0)
    {γ_values : ℕ → ℝ}
    (hγ_nonneg : ∀ p, 0 ≤ γ_values p)
    (h_not_bad : ¬Bad_ε_ABC c γ_values) :
    Real.log (twoTail c : ℝ)
      ≤ Real.log (rad c : ℝ)
        + ∑ p ∈ (Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Nat.divisors c)),
            γ_values p * Real.log (p : ℝ) := by
  -- まず基本的な不等式を使う：log(twoTail c) ≤ ∑_p (v_p(c) - 2)_+ * log p
  have h_log_basic := ABC.log_twoTail_le_excess_sum c hc
  -- twoTail c = ∏ p^{max(v_p(c) - 2, 0)} の定義から
  -- log(twoTail c) = ∑_{p|c} max(v_p(c) - 2, 0) * log p
  -- ¬Bad_ε_ABC より ∀p≥3, v_p(c) - 2 ≤ γ_values p
  have h_vp_bound := not_bad_abc_implies_vp_bound h_not_bad
  -- 各項で max(v_p(c) - 2, 0) を γ_values p で抑える
  calc Real.log (twoTail c : ℝ)
      ≤ ∑ p ∈ c.factorization.support, (((c.factorization p - 2) : ℕ) : ℝ) * Real.log (p : ℝ) := h_log_basic
    _ ≤ Real.log (rad c : ℝ)
        + ∑ p ∈ (Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Nat.divisors c)),
            γ_values p * Real.log (p : ℝ) := by
      -- ここで詳細な不等式の変形が必要
      -- 1) p = 2 の項を分離
      -- 2) p ≥ 3 の項で v_p(c) - 2 ≤ γ_values p を使う
      sorry

-- 実装内容は [Working Note](/Working-Note.md) を参照
-- 既存のブリッジ補題を使って証明する（3段ブリッジ方式）
lemma quality_le_of_not_bad
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hnb : ¬Bad_ε c γ_values) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  -- NOTE: 現在の Bad_ε は Vp (2*c+1の評価) を使うが、
  -- ABC品質不等式では c 自体の p-adic valuation が必要。
  -- この不一致により、現在の形では証明できない。
  --
  -- 解決策:
  -- 1) Bad_ε の定義を修正する（大きな変更）
  -- 2) Bad_ε_ABC を使った別の定理を作る（推奨）
  -- 3) 橋渡し補題を追加する
  --
  -- ここでは一旦 sorry で置き、quality_le_of_not_bad_abc を推奨する
  sorry

-- ABC品質不等式の正しい形（Bad_ε_ABC を使用）
lemma quality_le_of_not_bad_abc
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hγ_nonneg : ∀ p, 0 ≤ γ_values p)
    (hnb : ¬Bad_ε_ABC c γ_values) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  -- Working-Note の方針:
  -- 1) ¬Bad_ε_ABC から twoTail の対数バウンドを得る
  -- 2) 対数バウンドをべき乗バウンドに変換
  -- 3) 一般ブリッジ quality_le_of_pi_tail_general を使う

  -- まず、c ≠ 0 を示す
  have hc_ne : c ≠ 0 := by
    have hc_pos : 0 < c := by linarith [ha_pos, hb_pos, hrel]
    exact Nat.pos_iff_ne_zero.mp hc_pos

  -- a * b ≠ 0
  have hab_ne : a * b ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp ha_pos) (Nat.pos_iff_ne_zero.mp hb_pos)

  -- この証明は複雑で、多くの補助補題が必要
  -- 現時点では sorry で置き、段階的に実装する
  -- 代わりに quality_le_of_not_bad_with_tail / with_log を使うことを推奨
  sorry

-- ==========================================
-- ブリッジ核：既存APIで閉じる最小実装（sorry なし）
-- ==========================================

/-- ブリッジ核：π側（¬Bad）と tail 側（TailBound γ）と δ+γ≤ε から
    `quality ≤ 1+ε` を"その場"で閉じる。余計な展開をしない。 -/
lemma quality_le_of_not_bad_with_tail
    {a b c : ℕ} {ε δ γ : ℝ}
    (hsum : a + b = c) (hcop : Nat.Coprime a b) (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (htail : ABC.TailBound γ a b c)
    (hδγ_nonneg : 0 ≤ δ + γ) (hδγ_le : δ + γ ≤ ε) :
  ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  -- π側は ¬Bad から即座に出る
  have hπ : (ABC.piSqRad c : ℝ) ≤ (ABC.rad (a * b) : ℝ) ^ δ :=
    ABC.piSqRad_le_of_not_bad hcop hsum h_not_bad
  -- 解析ブリッジをそのまま適用
  exact ABC.quality_le_of_pi_tail_general
          hε_pos hsum hcop hπ htail hδγ_nonneg hδγ_le

/-- ログ境界を TailBound に変えるヘルパ。 -/
lemma tailbound_of_log_bound
    {a b c : ℕ} {γ : ℝ}
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hsum : a + b = c)
    (Hlog : Real.log (ABC.twoTail c : ℝ) ≤ γ * Real.log (ABC.rad (a*b) : ℝ)) :
  ABC.TailBound γ a b c := by
  -- a*b ≠ 0, c ≠ 0 を用意
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp ha_pos) (Nat.pos_iff_ne_zero.mp hb_pos)
  have hc0 : c ≠ 0 := by
    have hc_pos : 0 < c := by linarith [ha_pos, hb_pos, hsum]
    exact Nat.pos_iff_ne_zero.mp hc_pos
  -- 既存の変換で twoTail ≤ rad^γ
  exact ABC.twoTail_le_rad_pow_of_log_bound (hc0 := hc0) (_hab0 := hab0) Hlog

/-- ¬Bad + （ログ境界） + δ+γ≤ε で quality を閉じる便利版。 -/
lemma quality_le_of_not_bad_with_log
    {a b c : ℕ} {ε δ γ : ℝ}
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hsum : a + b = c) (hcop : Nat.Coprime a b) (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (Hlog : Real.log (ABC.twoTail c : ℝ) ≤ γ * Real.log (ABC.rad (a * b) : ℝ))
    (hδγ_nonneg : 0 ≤ δ + γ) (hδγ_le : δ + γ ≤ ε) :
  ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  have htail : ABC.TailBound γ a b c :=
    tailbound_of_log_bound ha_pos hb_pos hsum Hlog
  exact quality_le_of_not_bad_with_tail hsum hcop hε_pos h_not_bad htail hδγ_nonneg hδγ_le

end Chernoff

end ABC
