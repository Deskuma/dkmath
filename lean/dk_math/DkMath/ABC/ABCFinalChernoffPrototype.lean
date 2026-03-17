/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.ABC

set_option linter.style.emptyLine false
set_option linter.style.longLine false

open scoped BigOperators
open Finset
open Filter

#check @ABC.rpow_layer_cake
#check @ABC.div_le_iff
#check @ABC.ceil_spec

namespace ABC

-- 便利略記：p-進評価
@[simp] abbrev Vp (p n : ℕ) : ℕ := padicValNat p (2 * n + 1)

-- ==========================================
-- Task 1: MGF Bound with Explicit Constant
-- ==========================================

lemma mgf_padic_excess_bound_explicit
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
    {X : ℕ} (hX : X ≥ 3) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))
      ≤ 4 * (X + 1) := by
  -- rpow_layer_cake を使用して、層状展開により上界を得る
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < (p : ℝ) := by norm_cast; exact hp.pos
  have hp_one : 1 < (p : ℝ) := by norm_cast; omega

  -- V(n) := Vp p n（p-進評価）として定義
  let V := fun n => Vp p n

  -- V n ≤ X+1 の上界：p-進評価の性質から
  have hV_bd : ∀ n ≤ X, V n ≤ X + 1 := fun n hn => by
    -- V(n) = v_p(2n+1) ≤ log_p(2n+1) ≤ log_p(2X+1) ≤ X+1
    have h1 : V n ≤ Nat.log p (2*n+1) := padicValNat_le_nat_log (2*n+1)
    have h2 : 2*n+1 ≤ 2*X+1 := by omega
    have h3 : Nat.log p (2*n+1) ≤ Nat.log p (2*X+1) := by
      exact Nat.log_mono_right h2
    have h4 : Nat.log p (2*X+1) ≤ X + 1 := by
      -- p^{X+1} ≥ 2X+1 ⟹ log_p(2X+1) ≤ X+1
      have hp_gt_1 : 1 < p := by omega
      -- 対偶で証明: log p (2X+1) > X+1 を仮定して矛盾を導く
      by_contra h_not
      push_neg at h_not
      -- log p (2X+1) > X+1, so log p (2X+1) ≥ X+2
      have : X + 2 ≤ Nat.log p (2*X+1) := by omega
      -- By definition of log: p^{log p n} ≤ n
      have h_pow_le : p ^ Nat.log p (2*X+1) ≤ 2*X+1 := by
        apply Nat.pow_log_le_self
        omega
      -- But X+2 ≤ log p (2X+1) implies p^{X+2} ≤ p^{log p (2X+1)} ≤ 2X+1
      have h_bad : p ^ (X+2) ≤ 2*X+1 := by
        calc p ^ (X+2)
            ≤ p ^ Nat.log p (2*X+1) := Nat.pow_le_pow_right (Nat.Prime.pos hp) this
          _ ≤ 2*X+1 := h_pow_le
      -- But we know p^{X+1} ≥ 3^{X+1} ≥ 2X+1, and p^{X+2} > p^{X+1}
      have h_good : 2*X+1 < p ^ (X+2) := by
        have h_3_bound : 3 ^ (X+1) ≥ 2*X+1 := three_pow_ge_linear X
        have h_pow_bound : p ^ (X+1) ≥ 2*X+1 := by
          calc p ^ (X+1) ≥ 3 ^ (X+1) := Nat.pow_le_pow_left hp3 (X+1)
            _ ≥ 2*X+1 := h_3_bound
        calc 2*X+1 ≤ p ^ (X+1) := h_pow_bound
          _ < p ^ (X+2) := Nat.pow_lt_pow_right hp_gt_1 (by omega)
      omega
    omega

  -- rpow_layer_cake の適用
  have h_layer := ABC.rpow_layer_cake (p : ℝ) hp_one X t ht V hV_bd

  -- 層の和の幾何級数評価：r = p^{t-1} ≤ 2/3 より定数 3 を得る
  -- ABCTelescoping の補題を直接使用（引数を名前付きで渡す）
  -- Vp は abbrev（padicValNat p (2 * n + 1) の別名）であり、rw による書き換え用の等式が生成されないため、
  -- ここではそのまま h_telescoping を使用する。
  have h_telescoping := ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3 (p := p) (hp := ⟨hp⟩) (hp3 := hp3) (t := t) (ht := ht) (ht_le := ht_le) (X := X) (hX := hX)
  exact h_telescoping

lemma mgf_padic_excess_bound
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
    {X : ℕ} (hX : X ≥ 3) :
    (1 / (X + 1 : ℝ)) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))
      ≤ 4 := by
  have H := mgf_padic_excess_bound_explicit (p:=p) (hp3:=hp3) (t:=t) (ht:=ht) (ht_le:=ht_le) (X:=X) (hX:=hX)
  have hxpos : 0 < (X+1 : ℝ) := by exact_mod_cast (Nat.succ_pos X)
  calc (1 / (X + 1 : ℝ)) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))
      = (∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))) / (X + 1) := by ring
    _ ≤ (4 * (X + 1)) / (X + 1) := by
        apply div_le_div_of_nonneg_right H
        norm_cast; omega
    _ = 4 := by field_simp [hxpos.ne']

-- ==========================================
-- Task 2: Chernoff Bound for Single Prime
-- ==========================================

-- Markov(指数型)不等式：有限集合上の version（既に完成）
lemma card_filter_le_exp_markov
    {α}
    (s : Finset α) (Z : α → ℝ) (γ t : ℝ) (ht : 0 ≤ t) :
    (s.filter (fun a => Z a ≥ γ)).card
      ≤ Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by
  classical
  have h1 :
      (s.filter (fun a => Z a ≥ γ)).card
        ≤ ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0) := by
    -- The indicator sum counts exactly the filtered elements
    trans (∑ a ∈ s.filter (fun a => Z a ≥ γ), (1 : ℝ))
    · norm_cast
      simp [Finset.sum_const]
    · -- ∑ over filter ≤ ∑ over full set with indicator
      have : ∑ a ∈ s.filter (fun a => Z a ≥ γ), (1 : ℝ) = ∑ a ∈ s, (if Z a ≥ γ then 1 else 0) := by
        apply Finset.sum_filter
      exact le_of_eq this
  have h2 :
      ∀ a, (if Z a ≥ γ then (1 : ℝ) else 0)
          ≤ Real.exp (-t*γ) * Real.exp (t * Z a) := by
    intro a; by_cases h : Z a ≥ γ
    · -- When Z a ≥ γ: show 1 ≤ exp(-tγ) * exp(tZ a)
      simp only [h, ite_true]
      have : (1 : ℝ) ≤ Real.exp (t * (Z a - γ)) := by
        -- exp(x) ≥ 1 iff x ≥ 0
        rw [Real.one_le_exp_iff]
        apply mul_nonneg ht
        linarith
      -- exp(t(Z-γ)) = exp(-tγ) * exp(tZ)
      calc (1 : ℝ)
          ≤ Real.exp (t * (Z a - γ)) := this
        _ = Real.exp (t * Z a + (-t * γ)) := by ring_nf
        _ = Real.exp (t * Z a) * Real.exp (-t * γ) := by rw [Real.exp_add]
        _ = Real.exp (-t * γ) * Real.exp (t * Z a) := by ring
    · simp only [ge_iff_le, h, ↓reduceIte, neg_mul]; positivity
  have := Finset.sum_le_sum (s := s) (by intro a ha; exact h2 a)
  have : ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
           ≤ Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by
    calc ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
        ≤ ∑ a ∈ s, Real.exp (-t*γ) * Real.exp (t * Z a) := this
      _ = Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by rw [← Finset.mul_sum]
  exact le_trans h1 this


-- Chernoff 不等式（単一素数版、定数 C を明示的に与える版）

/-- Engine: from a per-prime MGF bound to a Chernoff tail bound.
    Assumes: for t ∈ (0, log2/log3],  ∑_{n≤X} p^{t·V_p(n)} ≤ A · (X+1).
    Then for X ≥ X0 with A·(X+1) ≤ U·X, we get
      #{n≤X : V_p-2 > γ} ≤ U · X · p^{-t(γ+2)}. -/
private lemma chernoff_engine
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    (γ : ℝ) (_hγ : 0 < γ)
    {t : ℝ} (ht : 0 < t) (_ht_le : t ≤ Real.log 2 / Real.log 3)
    {A U : ℝ} (_hA : 0 < A) (_hU : 0 < U)
    {X0 : ℕ}
    -- MGF bound provided from layer-cake etc. (uses Vp notation)
    -- only required for X ≥ X0 (we will instantiate X0 = 100 in callers)
    (hmgf : ∀ ⦃X⦄, X ≥ X0 → ∑ n ∈ Finset.Icc 0 X,
                    (p : ℝ) ^ (t * (Vp p n : ℤ)) ≤ A * (X + 1))
    -- absorb (X+1) into U·X beyond X0
    (habsorb : ∀ ⦃X⦄, X ≥ X0 → A * (X + 1 : ℝ) ≤ U * (X : ℝ)) :
    ∀ ⦃X⦄, X ≥ X0 →
      (Finset.filter
         (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
         (Finset.Icc 0 X)).card
      ≤ U * (X : ℝ) * (p : ℝ) ^ (-t * (γ + 2)) := by
  intro X hX
  -- 基本的な正の値
  have hp_pos : 0 < (p : ℝ) := by
    have h01 : (0 : ℕ) < (1 : ℕ) := by norm_num
    have hp_gt1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 3) hp3
    have hnat : (0 : ℕ) < p := lt_trans h01 hp_gt1
    exact_mod_cast hnat
  have hlogp_pos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_trans (by norm_num : 1 < 2) (by exact_mod_cast hp3)))

  -- Markov(指数)を適用
  have hMarkov := card_filter_le_exp_markov
    (s := Finset.Icc 0 X)
    (Z := fun n => Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
    (γ := γ * Real.log (p : ℝ))
    (t := t)
    (ht := le_of_lt ht)

  -- フィルタ条件の含意（> γ → ≥ γ）
  have hIncl : (Finset.filter
      (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ) (Finset.Icc 0 X)).card
    ≤ (Finset.filter
      (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
      (Finset.Icc 0 X)).card := by
    refine Finset.card_mono ?_
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have ⟨hnIcc, ⟨hn_le, hcond⟩⟩ := hn
    have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := by simpa using hcond
    have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
      mul_lt_mul_of_pos_left hgt' hlogp_pos
    have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
      simpa [mul_comm] using hmul
    exact ⟨hnIcc, this.le⟩  -- exp(t*Z) = p^{t(V-2)} = p^{-2t} * p^{tV}
  have hSum : ∑ n ∈ Finset.Icc 0 X,
      Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
    = (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
    classical
    have : ∀ n, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
            = (p:ℝ) ^ (t * (((Vp p n : ℤ) : ℝ) - 2)) := by
      intro n
      simp [Real.rpow_def_of_pos hp_pos, mul_comm, mul_assoc]
    calc _ = ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * (((Vp p n : ℤ) : ℝ) - 2)) := by
            apply Finset.sum_congr rfl; intro n _; exact this n
      _ = ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (-2 * t) * (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            apply Finset.sum_congr rfl; intro n _
            have h_exp : t * (((Vp p n : ℤ) : ℝ) - 2) = (-2 * t) + (t * ((Vp p n : ℤ) : ℝ)) := by ring
            rw [h_exp, Real.rpow_add hp_pos]
      _ = (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            simp [Finset.mul_sum]

  -- MGF bound を投入 (we only require it for X ≥ X0)
  have hMGF := hmgf (hX)

  -- Markov → MGF → 吸収
  have hExp_to_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
    simp [Real.rpow_def_of_pos hp_pos, mul_comm, mul_left_comm, mul_assoc]

  calc ((Finset.filter
        (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ) (Finset.Icc 0 X)).card : ℝ)
      ≤ ((Finset.filter
        (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card : ℝ) := by exact_mod_cast hIncl
    _ ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
        ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := hMarkov
    _ = (p:ℝ) ^ (-t * γ) * ((p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        rw [hExp_to_rpow, hSum]
    _ = (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by ring
    _ = (p:ℝ) ^ (-t * (γ + 2)) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
        have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
          rw [← Real.rpow_add hp_pos]; ring_nf
        rw [this]
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (A * (X + 1)) := by
        apply mul_le_mul_of_nonneg_left hMGF
        apply Real.rpow_nonneg; linarith
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (U * X) := by
        apply mul_le_mul_of_nonneg_left (habsorb hX)
        apply Real.rpow_nonneg; linarith
    _ = U * (X : ℝ) * (p : ℝ) ^ (-t * (γ + 2)) := by ring



-- Chernoff 不等式（単一素数版、定数 C を明示的に与える版のサンプル実装）
lemma chernoff_single_prime_explicit_proof_sample
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    (γ : ℝ) (_hγ : 0 < γ) :
    let t := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ 100,
        (Finset.filter
          (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
          (Finset.Icc 0 X)).card
        ≤ C * (X : ℝ) * (p : ℝ) ^ (-t * (γ + 2)) := by
  intro t
  -- 定数は 5 で行ける（X≥100 前提）。6 でも 8 でも可。
  refine ⟨5, by norm_num, ?_⟩
  intro X hX100
  have hp_pos : 0 < (p : ℝ) := by
    -- 自然数上で 0 < 1 ∧ 1 < p を組み立ててから実数へ変換する（simp の再帰問題回避）
    have h01 : (0 : ℕ) < (1 : ℕ) := by norm_num
    -- hp3 : p ≥ 3 から 1 < p を得る
    have hp_gt1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 3) hp3
    have hnat : (0 : ℕ) < p := lt_trans h01 hp_gt1
    exact_mod_cast hnat
  have hlogp_pos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_trans (by norm_num : 1 < 2) (by exact_mod_cast hp3)))

  -- log 3 > 0, log 2 > 0 の確認
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)

  -- t の上界評価 ：t = log2/(2*log3) ≤ log2/log3
  have ht_le : t ≤ Real.log 2 / Real.log 3 := by
    have : 0 < Real.log 3 := hlog3
    have : (Real.log 3) ≤ (2 * Real.log 3) := by nlinarith
    -- 0<log2, log3>0 なので分母が大きいと全体は小さくなる
    have : Real.log 2 / (2 * Real.log 3) ≤ Real.log 2 / Real.log 3 := by
      exact (div_le_div_of_nonneg_left (le_of_lt hlog2) hlog3 this)
    simpa using this

  -- 有界集合版マルコフ（≥ に緩め、∧ の X 制約は Icc に吸収）
  have hMarkov := card_filter_le_exp_markov
    (s := Finset.Icc 0 X)
    (Z := fun n => Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
    (γ := γ * Real.log (p : ℝ))
    (t := t) (ht := by
      -- t > 0
      have : 0 < Real.log 2 / (2 * Real.log 3) := by
        have hden : 0 < 2 * Real.log 3 := by nlinarith
        exact div_pos hlog2 hden
      exact (le_of_lt this))

  -- フィルタ条件の含意（> γ → ≥ γ）
  have hIncl :
    (Finset.filter (fun n => n ≤ X ∧ (↑(Int.subNatNat (Vp p n) 2) : ℝ) > γ) (Finset.Icc 0 X)).card
      ≤ (Finset.filter (fun n => Real.log (p:ℝ) * (↑(Int.subNatNat (Vp p n) 2) : ℝ) ≥ γ * Real.log (p:ℝ))
            (Finset.Icc 0 X)).card := by
    -- Icc 0 X にいるなら n ≤ X は自明、かつ hγ>0・log p>0 より >γ ⇒ ≥ γ のスカラー倍
    refine Finset.card_mono ?subset
    intro n hn
    -- hn は List.Mem なので、mem_filter と mem_Icc で展開しておく
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    -- hn : 0 ≤ n ∧ n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ
    rcases hn with ⟨_, hn_le, hcond⟩
    -- hcond : ((Vp p n : ℤ) : ℝ) - 2 > γ, so reverse it to γ < ...
    have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := by simpa using hcond
    -- multiply both sides by Real.log (p : ℝ) > 0 on the left
    have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
      mul_lt_mul_of_pos_left hgt' hlogp_pos
    -- rewrite to the form γ * Real.log (p : ℝ) < Real.log (p : ℝ) * (...)
    have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
      simpa [mul_comm] using hmul
    have : n ≤ X ∧ γ * Real.log (p:ℝ) ≤ Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
      ⟨hn_le, this.le⟩
    simpa [Finset.mem_filter] using this

  -- 右辺和の評価：exp(t*Z) = p^{t(V-2)} = p^{-2t} * p^{tV}
  have hSum :
    ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
      = (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
    -- rpow 定義で落として足し算に分解
    classical
    have hp' : 0 < (p:ℝ) := hp_pos
    have : ∀ n, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
            = (p:ℝ) ^ (t * (((Vp p n : ℤ) : ℝ) - 2)) := by
      intro n
      -- x^y = exp(y * log x)
      simp [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]
    calc
      _ = ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * (((Vp p n : ℤ) : ℝ) - 2)) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact this n
      _ = ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (-2 * t) * (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            apply Finset.sum_congr rfl; intro n hn;
            have h_exp : t * (((Vp p n : ℤ) : ℝ) - 2) = (-2 * t) + (t * ((Vp p n : ℤ) : ℝ)) := by ring
            rw [h_exp, Real.rpow_add hp']
      _ = (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            simp [Finset.mul_sum]
      -- 3> No goals
    -- 2> No goals

  -- 1> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ 5 * ↑X * ↑p ^ (-t * (γ + 2))


  -- MGF（rpow 版）上界を投入：∑ p^{t Vp} ≤ 4 (X+1)
  have hMGF := mgf_padic_excess_bound_explicit
              (p:=p)
              (hp3:=hp3)
              (t:=t)
              (ht := by
                -- t > 0 は上の証明と同じ
                have hden : 0 < 2 * Real.log 3 := by nlinarith
                exact div_pos hlog2 hden)
              (ht_le := ht_le)
              (X:=X)
              (hX:=by exact le_trans (by decide : (3:ℕ) ≤ 100) hX100)
  --
  -- まとめ：Markov → MGF → 定数吸収
  have hcard :
    (Finset.filter (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
      (Finset.Icc 0 X)).card
      ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
          ((p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
    -- 2> ⊢ ↑(#({n ∈ Icc 0 X | Real.log ↑p * (↑↑(Vp p n) - 2) ≥ γ * Real.log ↑p})) ≤ Real.exp (-t * (γ * Real.log ↑p)) * (↑p ^ (-2 * t) * ∑ n ∈ Icc 0 X, ↑p ^ (t * ↑↑(Vp p n)))
    calc
      (Finset.filter (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card
        ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) * ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := by
          exact hMarkov
      _ = Real.exp (-t * (γ * Real.log (p:ℝ))) * ((p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          rw [hSum]
      -- 3> No goals
    -- 2> No goals

  have hExp_to_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
    -- exp((−tγ) log p) = p^{−tγ}
    have hp' : 0 < (p:ℝ) := hp_pos
    simp [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]
    -- 2> No goals

  have : (Finset.filter
          (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ) (Finset.Icc 0 X)).card
      ≤ (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (4 : ℝ) * (X + 1) := by
    -- 2> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * 4 * (↑X + 1)
    -- hIncl → hcard → hSum → hMGF
    -- hIncl : ℕ ≤ ℕ, while hcard is coerced to ℝ; cast both inequalities to ℝ before composing
    have hIncl_real :
      ((Finset.filter (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ) (Finset.Icc 0 X)).card : ℝ)
      ≤ ((Finset.filter (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
            (Finset.Icc 0 X)).card : ℝ) := by
      -- 3> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ ↑(#({n ∈ Icc 0 X | Real.log ↑p * (↑↑(Vp p n) - 2) ≥ γ * Real.log ↑p}))
      norm_cast
      -- 3> No goals
    -- 2> ⊢ ''
    have hcard_real :
      ((Finset.filter (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
            (Finset.Icc 0 X)).card : ℝ)
        ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
            ((p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
      -- 3> ⊢ ↑(#({n ∈ Icc 0 X | Real.log ↑p * (↑↑(Vp p n) - 2) ≥ γ * Real.log ↑p})) ≤ Real.exp (-t * (γ * Real.log ↑p)) * (↑p ^ (-2 * t) * ∑ n ∈ Icc 0 X, ↑p ^ (t * ↑↑(Vp p n)))
      -- 型の不一致を解消するため、-2 * t を明示的に使う
      -- ↑(Int.negSucc 1) * t = -2 * t なので、rw で書き換えて証明
      have h_negSucc : (p:ℝ) ^ (↑(Int.negSucc 1) * t) = (p:ℝ) ^ (-2 * t) := by
        -- Int.negSucc 1 = -2
        simp only [Int.reduceNegSucc, Int.cast_neg, Int.cast_ofNat, neg_mul]
      -- ゴールの右辺には ↑p ^ (-2 * t) が既に現れているので、hcard をそのまま使う
      exact hcard
      -- 3> No goals
    -- 2> ⊢ ''
    -- hcard_real の右辺から Real.exp(...) を p^(-tγ) に置き換えた版を作成
    have hcard_real' :
      ((Finset.filter (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ)) (Finset.Icc 0 X)).card : ℝ)
      ≤ (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
      -- hExp_to_rpow を hcard_real に適用して形を揃える
      rw [hExp_to_rpow] at hcard_real
      exact (by rw [mul_assoc]; exact hcard_real)
      -- 3> No goals
    --2> ⊢ ''
    -- さらに hMGF を使って ∑ ... ≤ 4 * (X + 1)
    have h_final :
      (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))
      ≤ (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (4 : ℝ) * (X + 1) := by
      -- 3> ⊢ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * ∑ n ∈ Icc 0 X, ↑p ^ (t * ↑↑(Vp p n)) ≤ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * 4 * (↑X + 1)
      -- 係数 ↑p ^ (-t * γ) * ↑p ^ (-2 * t) を両辺に掛けて不等式を維持する
      have s_nonneg : 0 ≤ (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) := by positivity
      -- mul_le_mul_of_nonneg_left が生成する右辺は括弧付けが異なるため、
      -- mul_assoc を用いて期待する形 (… * 4 * (X+1)) に整形する
      have h_mul := mul_le_mul_of_nonneg_left hMGF s_nonneg
      simpa [mul_assoc] using h_mul
      -- 3> No goals

    -- まとめて le_trans で合成（hcard_real' を用いる）
    exact le_trans (le_trans hIncl_real hcard_real') h_final
    -- 2> No goals
  -- 1> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ 5 * ↑X * ↑p ^ (-t * (γ + 2))

  -- 定数吸収の部分証明：4*(X+1) ≤ 5*X （X≥100）
  -- 4*(X+1) ≤ 5*X （X≥100）で C=5 に吸収
  have hx : (4 : ℝ) * (↑X + 1) ≤ (5 : ℝ) * ↑X := by
    -- 2> ⊢ 4 * (↑X + 1) ≤ 5 * ↑X
    have : (4:ℝ) * (↑X + 1) = 4 * ↑X + 4 := by ring
    have h_nat : 4 * X + 4 ≤ 5 * X := by nlinarith [hX100]
    -- 型を実数に持ち上げる
    have h_real : (4 : ℝ) * ↑X + 4 ≤ 5 * ↑X := by exact_mod_cast h_nat
    rw [this]
    exact h_real
    -- 2> No goals
  -- したがって結論
  -- 1> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ 5 * ↑X * ↑p ^ (-t * (γ + 2))
  calc
    (Finset.filter
      (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
      (Finset.Icc 0 X)).card
    ≤ (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (4 : ℝ) * (X + 1) := by
    -- 2> ⊢ ↑(#({n ∈ Icc 0 X | n ≤ X ∧ ↑↑(Vp p n) - 2 > γ})) ≤ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * 4 * (↑X + 1)
      exact this
    -- 2> No goals
    _ = (p:ℝ) ^ (-t * (γ + 2)) * (4 : ℝ) * (X + 1) := by
      -- 3> ⊢ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * 4 * (↑X + 1) = ↑p ^ (-t * (γ + 2)) * 4 * (↑X + 1)
          -- p^{-tγ} * p^{-2t} * 4 * (X+1) = p^{-t(γ+2)} * 4 * (X+1)
          have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
        -- 4> ⊢ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) = ↑p ^ (-t * (γ + 2))
            -- rpow_add を使うために等式の両辺を入れ替える
            -- exp の積を exp の和に変換する補助等式
            have exp_mul_add :
              Real.exp (-(γ * (Real.log ↑p * t))) * Real.exp (-(2 * (Real.log ↑p * t)))
                = Real.exp (Real.log ↑p * (-(γ * t) + -(2 * t))) := by
          -- 5> ⊢ exp (-(γ * (Real.log ↑p * t))) * exp (-(2 * (Real.log ↑p * t))) = exp (Real.log ↑p * (-(γ * t) + -(2 * t)))
              -- exp(a) * exp(b) = exp(a + b)
              -- 左辺を exp(a) * exp(b) = exp(a + b) の形に変形してから書き換える
              rw [← Real.exp_add]
              congr 1
              -- -(γ * (Real.log ↑p * t)) + -(2 * (Real.log ↑p * t)) = Real.log ↑p * (-(γ * t) + -(2 * t))
              ring
          -- 5> No goals
        -- 4> ⊢ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) = ↑p ^ (-t * (γ + 2))
            -- rpow_add を使って p^(-t*γ) * p^(-2*t) = p^(-t*(γ+2)) を直接証明する
            have hp' : 0 < (p:ℝ) := hp_pos
            have h_left : -t * γ + (-2 * t) = -t * (γ + 2) := by ring
            simp only [neg_mul]
            -- ⊢ ↑p ^ (-(t * γ)) * ↑p ^ (-(2 * t)) = ↑p ^ (-(t * (γ + 2)))
            rw [← Real.rpow_add hp']
            -- ⊢ ↑p ^ (-(t * γ) + -(2 * t)) = ↑p ^ (-(t * (γ + 2)))
            congr 1
            -- ⊢ -(t * γ) + -(2 * t) = -(t * (γ + 2))
            ring
        -- 4> No goals
      -- 3> ⊢ ↑p ^ (-t * γ) * ↑p ^ (-2 * t) * 4 * (↑X + 1) = ↑p ^ (-t * (γ + 2)) * 4 * (↑X + 1)
          simpa [this, mul_comm, mul_left_comm, mul_assoc] using Or.inl this
      -- 3> No goals
    _ ≤ 5 * ↑X * ↑p ^ (-t * (γ + 2)) := by
      -- 3> ⊢ ↑p ^ (-t * (γ + 2)) * 4 * (↑X + 1) ≤ 5 * ↑X * ↑p ^ (-t * (γ + 2))
          -- 定数吸収部分証明を適用
          have s_nonneg : 0 ≤ (p:ℝ) ^ (-t * (γ + 2)) := by positivity
          -- 左辺を分配して右辺と同じ形にする
          -- multiply both sides of hx by the nonnegative factor (p ^ (-t*(γ+2))) to keep the inequality
          have h_mul := mul_le_mul_of_nonneg_left hx s_nonneg
          -- tidy up multiplication order and finish
          simpa [mul_assoc, mul_comm, mul_left_comm] using h_mul
      -- 3> No goals
    -- 2> No goals
  -- 1> No goals
-- 完全版の証明終了


-- ==========================================
-- Chernoff Bound - Clean Engine-Based Version
-- ==========================================

-- Explicit version with C=5 (using the engine)
lemma chernoff_single_prime_explicit_const5
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    (γ : ℝ) (hγ : 0 < γ) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∀ {X}, X ≥ 100 →
      (Finset.filter
        (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
        (Finset.Icc 0 X)).card
      ≤ 5 * (X : ℝ) * (p : ℝ) ^ (-t0 * (γ + 2)) := by
  intro t0 X hX
  -- Set parameters: t0, A=4 (from MGF), U=5, X0=100
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have ht0_pos : 0 < t0 := by
    have : 0 < 2 * Real.log 3 := by linarith
    exact div_pos hlog2 this
  have ht0_le : t0 ≤ Real.log 2 / Real.log 3 := by
    have : Real.log 3 ≤ 2 * Real.log 3 := by linarith
    exact div_le_div_of_nonneg_left (le_of_lt hlog2) hlog3 this
  -- MGF bound: we only need the MGF for X ≥ 100, and mgf_padic_excess_bound_explicit
  -- supplies the needed bound for X ≥ 3, hence for X ≥ 100 in particular.
  have hmgf : ∀ ⦃X'⦄, X' ≥ 100 → ∑ n ∈ Finset.Icc 0 X', (p : ℝ) ^ (t0 * (Vp p n : ℤ)) ≤ 4 * (X' + 1) := by
    intro X' hX'
    have hX'_ge3 : X' ≥ 3 := by linarith
    exact mgf_padic_excess_bound_explicit (p:=p) (hp3:=hp3)
      (t:=t0) (ht:=ht0_pos) (ht_le:=ht0_le) (X:=X') (hX:=hX'_ge3)
    -- X' < 3 は実際には使われない（X ≥ 100）

  -- Absorb: 4·(X+1) ≤ 5·X for X≥100
  have habsorb : ∀ ⦃X : ℕ⦄, X ≥ 100 → (4 : ℝ) * (↑X + 1) ≤ 5 * ↑X := by
    intro X hX
    -- 型を ℝ に持ち上げて証明
    have h_nat : 4 * X + 4 ≤ 5 * X := by nlinarith
    -- lift the nat inequality to ℝ
    have h_real : (4 : ℝ) * ↑X + 4 ≤ 5 * ↑X := by exact_mod_cast h_nat
    -- rewrite 4*(X+1) in reals to match the goal, then finish
    have this : (4 : ℝ) * (↑X + 1) = (4 : ℝ) * ↑X + 4 := by ring
    rw [this]
    exact h_real

  -- Invoke the engine with A=4, U=5, X0=100
  exact @chernoff_engine p _ hp3 γ hγ t0 ht0_pos ht0_le
    4 5 (by norm_num) (by norm_num) 100 hmgf habsorb (X := X) hX -- Original explicit (∃C version) wraps the const5 version


-- Explicit version with C=5 (for X≥100)
lemma chernoff_single_prime_explicit
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    (γ : ℝ) (hγ : 0 < γ) :
    let t := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ 100,
        (Finset.filter
          (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
          (Finset.Icc 0 X)).card
        ≤ C * (X : ℝ) * (p : ℝ) ^ (-t * (γ + 2)) := by
  intro t
  refine ⟨5, by norm_num, ?_⟩
  intro X hX
  exact @chernoff_single_prime_explicit_const5 p _ hp3 γ hγ X hX


-- Uniform version with explicit constant C=5 (for X≥100)
lemma chernoff_single_prime_uniform'
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    (γ : ℝ) (hγ : 0 < γ)
    (X : ℕ) (hX : X ≥ 100) :
    let t := Real.log 2 / (2 * Real.log 3)
    (Finset.filter
      (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ)
      (Finset.Icc 0 X)).card
    ≤ (5 : ℝ) * (X : ℝ) * (p : ℝ) ^ (-t * (γ + 2)) := by
  intro t
  -- explicit_const5 を直接使用
  exact @chernoff_single_prime_explicit_const5 p _ hp3 γ hγ X hX



-- remove lemma chernoff_single_prime_explicit'



-- ==========================================
-- Task 3: Union Bound over Primes
-- ==========================================

lemma union_bound_chernoff
    (γ_values : ℕ → ℝ) (hγ_vals : ∀ p, 0 < γ_values p) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ 100,
        (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
          ((Finset.filter
            (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p)
            (Finset.Icc 0 X)).card : ℝ))
        ≤ C * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
             (p : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by
  -- uniform 版を使って C = 5
  let t := Real.log 2 / (2 * Real.log 3)
  use 5
  constructor
  · norm_num
  · intro X hX
    -- ∑_p card_p ≤ 5 * X * ∑_p p^{-t(γ_p+2)} where γ_p = γ_values p
    calc ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
          ((Finset.filter
            (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p)
            (Finset.Icc 0 X)).card : ℝ)
        ≤ ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            5 * (X : ℝ) * (p : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by
          apply Finset.sum_le_sum
          intro p hp
          -- chernoff_single_prime_uniform を各素数ごとに適用
          simp only [Finset.mem_filter, Finset.mem_range] at hp
          have ⟨_, ⟨hpPrime, hp3⟩⟩ := hp
          have hpFact : Fact p.Prime := ⟨hpPrime⟩
          -- use the uniform bound per-prime with γ = γ_values p
          exact @chernoff_single_prime_uniform' p hpFact hp3 (γ_values p) (hγ_vals p) X hX
      _ = 5 * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            (p : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by
          rw [← Finset.mul_sum]

-- ==========================================
-- Task 4: Exceptional Set via Borel–Cantelli
-- ==========================================

def Bad_ε (n : ℕ) (γ_values : ℕ → ℝ) : Prop :=
  ∃ p ≥ 3, p.Prime ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p

-- Provide a classical decidability instance so Finset.filter can be used with Bad_ε.
-- This is noncomputable/classical but appropriate for the combinatorial arguments below.
noncomputable instance decidable_Bad_ε (γ_values : ℕ → ℝ) : DecidablePred fun n => Bad_ε n γ_values :=
  fun n => Classical.dec (Bad_ε n γ_values)


-- debug
-- set_option pp.all true
-- set_option trace.convert true -- 使えない


-- Density version (実用的かつ証明可能)
/--
`bad_set_density_bound` は、与えられた実数 ε > 0、関数 γ_values : ℕ → ℝ（各素数 p に対して γ_values p > 0）、
および特定の級数評価条件のもとで、集合 `{ n ∈ [0, X] | Bad_ε n γ_values }` の濃度が X に対して C * X で上から抑えられることを示す補題です。

この補題は、Bad_ε n γ_values という性質を満たす整数 n の個数が、X が十分大きいときに線形な上界を持つことを保証します。
ここで、級数条件は、p が 3 以上の素数に対して、`∑ p ((p : ℕ) : ℝ) ^ (-(log 2 / (2 * log 3)) * (γ_values p + 2)) ≤ 1` という形で与えられています。

この結果は、数論的な集合の密度評価や、特定の条件を満たす整数の分布に関する研究に有用です。
-/
lemma bad_set_density_bound
    (ε : ℝ) (_hε : 0 < ε)
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p)
    (hseries : ∀ N, ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (N + 1)),
            ((p : ℕ) : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) ≤ 1) :
    ∃ C > 0, ∀ (X : ℕ), X ≥ 100 →
      ((Finset.filter (fun n
        => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
        ≤ C * (X : ℝ) := by
  -- ⊢ ∃ C > 0, ∀ X ≥ 100, ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C * ↑X

  -- classical

  -- debug
  -- define the relevant sets: primes P up to 2*X+1, and for each p in P the set S_p of bad n
  -- Use the global (noncomputable) instance so the instance term is definitionally equal
  -- to other uses of `decidable_Bad_ε γ_values` in this file. This avoids mismatches
  -- between locally-built `DecidablePred` values and the global one, which can
  -- make `exact` fail while `convert` still succeeds.
  haveI := decidable_Bad_ε γ_values
  -- #check this

  -- Use the union_bound_chernoff result (gives a per-X bound for sums over primes ≤ X)
  have ⟨C_union, hC_pos, hC_bound⟩ := union_bound_chernoff γ_values hγ_values
  -- we will count primes up to 2*X+1 (this covers any prime dividing 2*n+1 for n ≤ X)
  let C_final := 3 * C_union
  use C_final
  -- ⊢ C_final > 0 ∧ ∀ X ≥ 100, ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X
  constructor
  · -- ⊢ C_final > 0
    -- prove positivity of C_final
    -- C_final = 3 * C_union > 0
    linarith [hC_pos]
  · -- ⊢ ∀ X ≥ 100, ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X
    intro X hX
    -- ⊢ ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X
    -- goal: ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X

    -- primes considered up to 2*X+1 to capture any witness p for n ≤ X
    let P := Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (2 * X + 2))
    let S := fun p => (Finset.filter (fun n => n ≤ X ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X))
    -- show the bad set is contained in the bUnion over these primes
    have h_sub : (Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X))
      ⊆ P.biUnion S := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      rcases hn with ⟨hnIcc, hbad⟩
      rcases hbad with ⟨p, ⟨hp_ge3, ⟨hpPr, hcond⟩⟩⟩
      -- for n ≤ X any prime dividing 2*n+1 satisfies p ≤ 2*n+1 ≤ 2*X+1
      have h2n_le : 2 * n + 1 ≤ 2 * X + 1 := by linarith [hnIcc]
      -- from hcond and positivity of γ_values p we get Vp p n > 2 (as a real inequality)
      have h_vpn_gt2 : ((Vp p n : ℤ) : ℝ) > 2 := by linarith [hcond, hγ_values p]
      -- convert the real inequality to a nat inequality 2 < Vp p n using exact_mod_cast
      have h_vpn_nat_gt2 : 2 < Vp p n := by exact_mod_cast h_vpn_gt2
      -- hence Vp p n ≥ 3
      have h_vpn_ge3 : Vp p n ≥ 3 := Nat.succ_le_of_lt h_vpn_nat_gt2
      -- hence padicValNat p (2*n+1) ≥ 1, so p^1 ∣ 2*n+1 (use padicValNat_dvd_iff_le)
      have h_nonzero : 2 * n + 1 ≠ 0 := by linarith
      have hvp_nat1 : 1 ≤ padicValNat p (2 * n + 1) := by linarith [h_vpn_ge3]
      have hpow : p ^ 1 ∣ 2 * n + 1 := (padicValNat_dvd_iff_le (p := p) (hp := ⟨hpPr⟩) h_nonzero).mpr hvp_nat1
      -- from p^1 ∣ m we get p ∣ m (since p^1 = p)
      have h_dvd : p ∣ 2 * n + 1 := by simpa [pow_one] using hpow
      -- therefore p ≤ 2*n+1 and p ≤ 2*X+1
      have hp_le : p ≤ 2 * X + 1 := by
        have : p ≤ 2 * n + 1 := Nat.le_of_dvd (by linarith) h_dvd
        exact le_trans this h2n_le
      have hp_in_range : p < 2 * X + 2 := Nat.lt_succ_of_le hp_le
      have hp_in_P : p ∈ P := by
        have : p ∈ Finset.range (2 * X + 2) := Finset.mem_range.mpr hp_in_range
        exact Finset.mem_filter.mpr ⟨this, ⟨hpPr, hp_ge3⟩⟩
      have hn_in_S : n ∈ S p := by
        have hnIcc' : n ∈ Finset.Icc 0 X := Finset.mem_Icc.mpr hnIcc
        exact Finset.mem_filter.mpr ⟨hnIcc', ⟨hnIcc.2, hcond⟩⟩
      exact Finset.mem_biUnion.2 ⟨p, ⟨hp_in_P, hn_in_S⟩⟩
    -- now bound card via bUnion ≤ sum of cards
    have h_bUnion_le_sum : (P.biUnion S).card ≤ ∑ p ∈ P, (S p).card := by
      apply Finset.card_biUnion_le
    have h_left_le_bUnion : (Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card ≤ (P.biUnion S).card := by
      apply Finset.card_mono
      exact h_sub
    have h_union_le_sum : ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
        ≤ ∑ p ∈ P, ((S p).card : ℝ) := by
      calc ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
          ≤ ((P.biUnion S).card : ℝ) := by exact_mod_cast h_left_le_bUnion
        _ ≤ (∑ p ∈ P, (S p).card : ℝ) := by exact_mod_cast h_bUnion_le_sum

    -- apply union_bound_chernoff for X' = 2*X+1 (note X' ≥ 100)
    let X' := 2 * X + 1
    have hX' : X' ≥ 100 := by
      -- X' = 2 * X + 1, X ≥ 100 なら 2 * X + 1 ≥ 2 * 100 + 1 = 201 ≥ 100
      calc X' = 2 * X + 1 := rfl
           _ ≥ 2 * 100 + 1 := by gcongr
           _ = 201 := by norm_num
           _ ≥ 100 := by norm_num
    have h_sum_bound' := hC_bound X' hX'

    -- relate P to the Finset used by h_sum_bound' (P = primes ≤ X')
    have P_eq : P = Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X' + 1)) := by simp [P, X']

    have h_S_le : ∀ p ∈ P, (S p).card ≤ (Finset.filter (fun n => n ≤ X' ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X')).card := by
      intro p hp
      -- show S p ⊆ target filter (element-wise)
      have sub : S p ⊆ Finset.filter (fun n => n ≤ X' ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X') := by
        intro n hn
        -- hn : n ∈ S p = filter (cond) (Icc 0 X)
        have hfn := Finset.mem_filter.1 hn
        have hnIcc := hfn.1
        have hn_prop := hfn.2
        -- decompose Icc and props
        have h0 := (Finset.mem_Icc.1 hnIcc).1
        have hXn := (Finset.mem_Icc.1 hnIcc).2
        have hcond' := hn_prop.2
        -- n ≤ X' follows from n ≤ X and X ≤ X'
        have hX_le : X ≤ X' := by dsimp [X']; linarith
        have hXn' : n ≤ X' := le_trans hXn hX_le
        -- construct membership in target filter
        exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h0, hXn'⟩, ⟨hXn', hcond'⟩⟩
      apply Finset.card_mono
      exact sub

    have h_sum_compare : ∑ p ∈ P, (S p).card ≤ ∑ p ∈ P, (Finset.filter (fun n => n ≤ X' ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X')).card := by
      apply Finset.sum_le_sum; intro p hp; exact h_S_le p hp

    -- now apply h_sum_bound' (P = primes ≤ X') to the right-hand sum
    have h_prime_sum_bound : (∑ p ∈ P, (Finset.filter (fun n => n ≤ X' ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X')).card : ℝ)
      ≤ C_union * (X' : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X' + 1)),
        ((p : ℕ) : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by
      -- h_sum_bound' gives the same inequality; rewrite using P_eq
      have h_bound := h_sum_bound'
      rw [← P_eq] at h_bound
      exact h_bound

    -- combine the inequalities
    have h_series' : ∑ p ∈ P, ((p : ℕ) : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) ≤ 1 := by
      rw [P_eq]; apply hseries


    -- Build the final inequality directly for the target expression
    have : ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ) ≤ C_final * (X : ℝ) := by
      -- ⊢ ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X
      calc
        ((Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ)
          ≤ (∑ p ∈ P, ((S p).card : ℝ)) := h_union_le_sum
        _ ≤ (∑ p ∈ P, (Finset.filter (fun n => n ≤ X' ∧ ((Vp p n : ℤ) : ℝ) - 2 > γ_values p) (Finset.Icc 0 X')).card : ℝ) := by exact_mod_cast h_sum_compare
        _ ≤ C_union * (X' : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X' + 1)), ((p : ℕ) : ℝ) ^ (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p + 2)) := by exact_mod_cast h_prime_sum_bound
        _ ≤ C_union * (X' : ℝ) * 1 := by apply mul_le_mul_of_nonneg_left h_series' (mul_nonneg (le_of_lt hC_pos) (by positivity))
        _ = C_union * (X' : ℝ) := by ring
        _ ≤ C_union * (3 * (X : ℝ)) := by
          -- prove X' ≤ 3*X on ℕ, cast to ℝ, then multiply
          have nat_le : X' ≤ 3 * X := by dsimp [X']; linarith [hX]
          have real_le : (X' : ℝ) ≤ 3 * (X : ℝ) := by exact_mod_cast nat_le
          exact mul_le_mul_of_nonneg_left real_le (le_of_lt hC_pos)
        _ = C_final * (X : ℝ) := by ring

  -- 結論

    -- debug
    -- #check this                                                     -- this : ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X
    -- #check (↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X)  --        ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X : Prop

    -- ゴールの型を仮定に合わせる（うまく行かない）

    -- change ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X at *  -- 変化無し
    -- show (↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X) -- error
    -- show は機能しなかった。

    -- try exact this  -- error: instance term mismatch (DecidablePred)
    -- try exact_mod_cast this  -- error: instance term mismatch (DecidablePred)

    -- (↑(Finset.filter (fun n => Bad_ε n γ_values) (Finset.Icc 0 X)).card : ℝ) ≤ C_final * (X : ℝ)
    -- ⊢ ↑(#({n ∈ Icc 0 X | Bad_ε n γ_values})) ≤ C_final * ↑X

    convert this  -- No goals / Goals accomplished!

    -- 理由: Finset.filter の述語の DecidablePred instance が定義的に一致しないため exact できない。
    -- Lean の instance 解決の仕様によるもので、convert なら等価として吸収できる。


  -- これで証明終了

end ABC
