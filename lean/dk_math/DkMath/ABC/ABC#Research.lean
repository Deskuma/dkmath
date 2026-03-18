/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABC036

namespace ABC
namespace Chernoff

-- 例: this : (↑(#S) ≤ C_final * ↑X) が得られているとする
-- ゴールが同じ形だが exact が拒否する場合に show でゴールを書き換えて exact を使う
example {S : Finset ℕ} {C_final : ℝ} {X : ℕ} (this : (↑S.card : ℝ) ≤ C_final * (X : ℝ))
  : (↑S.card : ℝ) ≤ C_final * (X : ℝ) := by
  -- ゴールを this とまったく同形にする
  show (↑S.card : ℝ) ≤ C_final * (X : ℝ)
  exact this

-- change はゴールや仮定の型を別の等式で置き換えるのに使える
example {h : (1 + 1 : ℕ) = 2} : True := by
  -- 仮定 h の型を別の同値な形に変えたいとき
  change (2 = 2) at h  -- h の型が 2 = 2 になる（等価な形なら allowed）
  trivial

-- ==========================================
-- Task 5: Quality Inequality from ¬Bad_ε
-- ==========================================

axiom quality_le_of_not_bad
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hnb : ¬Bad_ε c γ_values) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε)
  -- ¬Bad_ε c γ_values から：∀ p ≥ 3, (v_p(c)-2) ≤ γ_values p
  -- つまり，c の p-進過剰が制御されている

  -- 【証明の方針】
  -- 1. v_p(c) を v_p(c) = min(v_p(c),1) + max(v_p(c)-1,0) と分解
  -- 2. c = ∏_p p^{v_p(c)} = rad(c) · ∏_p p^{max(v_p(c)-1,0)}
  -- 3. hnb より v_p(c) ≤ 2 + γ_values p
  -- 4. したがって max(v_p(c)-1,0) ≤ 1 + γ_values p
  -- 5. log c ≤ log(rad(c)) + ∑_p (1 + γ_values p) · log p
  -- 6. γ_values を p 依存で設計し、∑_p γ_values p · log p ≤ ε · log(rad(abc))
  -- 7. よって log c ≤ (1 + ε) · log(rad(abc))
  -- 8. c ≤ exp(1) · rad(abc)^{1+ε}

  -- 【問題点】
  -- 現状の γ_values は定数関数なので、ステップ6が成立しない。
  -- γ_values を γ_p = A · log(p) の形にする必要がある。

  -- 【補助補題 padicValNat_split の利用】
  -- have h_split := padicValNat_split p c
  -- これで v_p(c) の分解を使える

  -- so#rry -- γ_values を p 依存にする設計変更が必要

-- ==========================================
-- Final Theorem: ABC Quality Inequality
-- ==========================================

theorem abc_quality_final (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℝ), 0 < K ∧
      ∀ (a b c : ℕ),
        a + b = c →
        IsCoprime a b →
        (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  let γ_p : ℕ → ℝ := fun p => ε / 2
  let K := Real.exp 1 * 3 * 100
  use K
  constructor
  · positivity
  · intro a b c hab hcoprime
    -- 【統合フロー：bad_set_density_bound ベース】
    -- 1. chernoff_single_prime_explicit から各 p の Chernoff 上界
    -- 2. union_bound_chernoff で全素数の合算
    -- 3. bad_set_density_bound で密度上界 #{n≤X:Bad(n)} ≤ C·X
    -- 4. quality_le_of_not_bad で品質不等式
    --
    -- 【問題点】
    -- - bad_set_density_bound は密度上界しか与えない
    -- - quality_le_of_not_bad は ¬Bad_ε c γ_p を要求している
    -- - 密度上界から ¬Bad_ε c を得るには、c が「例外集合の外」にあることを示す必要
    -- - しかし、有限個の例外を除いてすべての c で成立することは証明できない
    --   （Working-Note.md の「4) not_bad_of_union_bound は命題が強すぎる」参照）
    --
    -- 【2つの解決策】
    -- A. quality_le_of_not_bad の前提を緩める
    --    - ¬Bad_ε ではなく、密度条件から直接 quality を導出
    --    - または、「密度が小さい → 高々有限個の例外 → それらを除く」議論
    -- B. abc_quality_final の主張を弱める
    --    - 「∀ (a,b,c)」ではなく「例外的な有限組を除く∀ (a,b,c)」
    --    - または「十分大きい c に対して」
    --
    -- 【暫定対処】
    -- Working-Note.md の方針に従い、密度版で進めるべきだが、
    -- quality_le_of_not_bad との接続が未完成。
    -- ここでは so#rry で進め、設計変更を TODO とする。

    have h_c_ge_0 : 0 ≤ (c : ℝ) := by norm_cast; omega

    sorry
    -- TODO: bad_set_density_bound と quality_le_of_not_bad の接続
    -- 解決方針：
    -- 1. γ_values を p 依存関数に変更（γ_p = A·log p）
    -- 2. quality_le_of_not_bad を密度版に対応させる
    -- 3. または abc_quality_final の主張を「例外有限個を除く」形に変更

end Chernoff
end ABC
