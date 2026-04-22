/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC022
import DkMath.ABC.PadicTelescoping
import DkMath.ABC.ChernoffBasic

#print "file: DkMath.ABC.ChernoffSinglePrime"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

namespace Chernoff
open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

axiom mgf_padic_excess_bound_uniform
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (t : ℝ) (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
    (X : ℕ) (hX : const_X ≤ X) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ)) ≤ 4 * (X + 1)


/--
`mgf_padic_excess_bound_explicit` 補題は、p進付値 `Vp p n` を用いた和
`∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))` の上界を与えます。
ここで `p` は素数 (かつ `p ≥ 3`)、`t` は正の実数で `t ≤ log 2 / log 3` を満たし、
`X` は 3 以上の自然数です。

この補題は、確率論や数論的な Chernoff 型評価において、p進付値のモーメント母関数の
「過剰分布」の明示的な上界を与えるために用いられます。
証明は一様な方法に基づいています。

- `p` : 素数 (かつ `p ≥ 3`)
- `t` : 正の実数 (`0 < t ≤ log 2 / log 3`)
- `X` : 3 以上の自然数
- `Vp p n` : n の p進付値
-/
lemma mgf_padic_excess_bound_explicit -- (uniform proof)
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
    {X : ℕ} (hX : X ≥ 3) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ)) ≤ 4 * (X + 1) := by
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
      push Not at h_not
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


-- Final MGF bound lemma: normalized version
/--
`mgf_padic_excess_bound` は、素数 `p`（`p ≥ 3`）と実数 `t`（`0 < t ≤ log 2 / log 3`）、自然数 `X`（`X ≥ 3`）に対して、以下の不等式を示します：

$$
\frac{1}{X+1} \sum_{n=0}^{X} p^{t \cdot V_p(n)} \leq 4
$$

ここで $V_p(n)$ は $n$ の $p$ 進指数関数（$p$ で割り切れる回数）を表します。

この補題は、$p$ 進評価に基づく確率的なモーメント生成関数（MGF）の上限評価に関するものです。特に、$t$ の範囲と $X$ の下限により、和の値が $4$ 以下に抑えられることを保証します。

この結果は、$p$ 進数や確率論的手法を用いた解析において、Chernoff型の評価や大数の法則の応用に役立ちます。
-/
lemma mgf_padic_excess_bound
    {p : ℕ} [Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3)
    {X : ℕ} (hX : X ≥ 3) :
    (1 / (X + 1 : ℝ)) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ)) ≤ 4 := by
  -- Use the explicit MGF bound to get the desired inequality
  have H := mgf_padic_excess_bound_explicit (p:=p) (hp3:=hp3) (t:=t) (ht:=ht) (ht_le:=ht_le) (X:=X) (hX:=hX)
  have hxpos : 0 < (X+1 : ℝ) := by exact_mod_cast (Nat.succ_pos X)
  calc (1 / (X + 1 : ℝ)) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))
      = (∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (Vp p n : ℤ))) / (X + 1) := by ring
    _ ≤ (4 * (X + 1)) / (X + 1) := by
        apply div_le_div_of_nonneg_right H
        norm_cast; omega
    _ = 4 := by field_simp [hxpos.ne']

lemma chernoff_engine
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
  have hp_pos : 0 < (p : ℝ) := prime_rpos (Fact.out : Nat.Prime p)
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
    exact ⟨hnIcc, this.le⟩

  -- exp(t*Z) = p^{t(V-2)} = p^{-2t} * p^{tV}
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

open Classical in
lemma chernoff_single_prime_uniform
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (_hγ : 0 < γ)
    (t : ℝ) (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3) :
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  classical
  use const_C
  constructor
  · rfl
  constructor
  · rw [const_C]; norm_num
  · intro X hX
    have hp_pos : 0 < (p : ℝ) := by
      have hp : Nat.Prime p := Fact.out
      exact_mod_cast hp.pos
    have hlogp_pos : 0 < Real.log (p : ℝ) := by
      apply Real.log_pos
      calc (1 : ℝ) < 3 := by norm_num
        _ ≤ p := by exact_mod_cast hp3
    have hMGF := mgf_padic_excess_bound_uniform (p := p) hp3 t ht ht_le X (by exact hX)
    have habsorb : (4 : ℝ) * (X + 1) ≤ const_C * X := by
      exact absorb_constant_4_to_5 X hX
    have hExp_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
      have hp' : 0 < (p:ℝ) := hp_pos
      simp only [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]
    have hIncl : (Finset.filter
        (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card
      ≤ (Finset.filter
        (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card := by
      refine Finset.card_mono ?_
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have ⟨hnIcc, ⟨_, hcond⟩⟩ := hn
      have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := hcond
      have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
        mul_lt_mul_of_pos_left hgt' hlogp_pos
      have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
        simpa [mul_comm] using hmul
      exact ⟨hnIcc, this.le⟩
    have hMarkov := card_filter_le_exp_markov
      (s := Finset.Icc 0 X)
      (Z := fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
      (γ := γ * Real.log (p:ℝ))
      (t := t)
      (ht := le_of_lt ht)
    calc ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ((Finset.filter
          (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
          (Finset.Icc 0 X)).card : ℝ) := by exact_mod_cast hIncl
      _ ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
          ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := hMarkov
      _ = Real.exp (-t * (γ * Real.log (p:ℝ))) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          have hp_pos' : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos (Fact.out : Nat.Prime p)
          have h_exp_rpow : ∀ n, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) =
              (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) * (p : ℝ) ^ (-2 * t) := by
            intro n
            let v := ((Vp p n : ℤ) : ℝ)
            have : t * (Real.log (p : ℝ) * (v - 2)) = (t * (v - 2)) * Real.log (p : ℝ) := by ring
            rw [this]
            rw [mul_comm (t * (v - 2)) (Real.log (p : ℝ))]
            rw [← Real.rpow_def_of_pos hp_pos']
            have : (p : ℝ) ^ (t * (v - 2)) = (p : ℝ) ^ (t * v) * (p : ℝ) ^ (-2 * t) := by
                rw [← Real.rpow_add hp_pos' (t * v) (-2 * t)]
                congr 1
                ring
            rw [this]
          have h_sum :
            ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
            = (p : ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            rw [Finset.sum_congr rfl (fun n _ => h_exp_rpow n), ← Finset.sum_mul, mul_comm]
          rw [h_sum, ←mul_assoc, hExp_rpow]
      _ = (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          rw [hExp_rpow]
      _ = (p:ℝ) ^ (-t * (γ + 2)) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
            rw [← Real.rpow_add hp_pos]
            congr 1
            ring
          rw [this]
      _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (4 * (X + 1)) := by
          apply mul_le_mul_of_nonneg_left hMGF
          apply Real.rpow_nonneg; linarith
      _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (5 * X) := by
          apply mul_le_mul_of_nonneg_left habsorb
          apply Real.rpow_nonneg; linarith
      _ = 5 * (X : ℝ) * ((p:ℝ) ^ (-t * (γ + 2))) := by ring
      _ ≤ 5 * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · have hp_pos' : 0 < (p : ℝ) := hp_pos
          have h_eq_rpow_exp : (p : ℝ) ^ (-t * (γ + 2)) = Real.exp (-t * γ * Real.log (p : ℝ) - 2 * t * Real.log (p : ℝ)) := by
            rw [Real.rpow_def_of_pos hp_pos']
            ring_nf
          have h_exp_le : Real.exp (-t * γ * Real.log (p : ℝ) - 2 * t * Real.log (p : ℝ)) ≤ Real.exp (-t * γ * Real.log (p : ℝ)) := by
            apply Real.exp_le_exp.mpr; nlinarith
          have h_pow_le_exp : (p : ℝ) ^ (-t * (γ + 2)) ≤ Real.exp (-t * γ * Real.log (p : ℝ)) := by
            rw [h_eq_rpow_exp]; exact h_exp_le
          exact h_pow_le_exp
        · norm_num

open Classical in
lemma chernoff_single_prime_uniform_rpow
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (_hγ : 0 < γ)
    (t : ℝ) (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3) :
    ∀ (X : ℕ), X ≥ const_X →
      ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p:ℝ) ^ (-t * (γ + 2)) := by
  classical
  intro X hX
  have hp_pos : 0 < (p : ℝ) := by
    have hp : Nat.Prime p := Fact.out
    exact_mod_cast hp.pos
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    calc (1 : ℝ) < 3 := by norm_num
      _ ≤ p := by exact_mod_cast hp3
  have hMGF := mgf_padic_excess_bound_uniform (p := p) hp3 t ht ht_le X (by exact hX)
  have habsorb : (4 : ℝ) * (X + 1) ≤ const_C * X := by
    exact absorb_constant_4_to_5 X hX
  have hExp_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
    have hp' : 0 < (p:ℝ) := hp_pos
    simp only [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]
  have hIncl : (Finset.filter
      (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card
    ≤ (Finset.filter
      (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
      (Finset.Icc 0 X)).card := by
    refine Finset.card_mono ?_
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have ⟨hnIcc, ⟨_, hcond⟩⟩ := hn
    have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := hcond
    have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
      mul_lt_mul_of_pos_left hgt' hlogp_pos
    have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
      simpa [mul_comm] using hmul
    exact ⟨hnIcc, this.le⟩
  have hMarkov := card_filter_le_exp_markov
    (s := Finset.Icc 0 X)
    (Z := fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
    (γ := γ * Real.log (p:ℝ))
    (t := t)
    (ht := le_of_lt ht)
  calc ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
      ≤ ((Finset.filter
        (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card : ℝ) := by exact_mod_cast hIncl
    _ ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
        ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := hMarkov
    _ = Real.exp (-t * (γ * Real.log (p:ℝ))) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        have hp_pos' : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos (Fact.out : Nat.Prime p)
        have h_exp_rpow : ∀ n, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) =
            (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) * (p : ℝ) ^ (-2 * t) := by
          intro n
          let v := ((Vp p n : ℤ) : ℝ)
          have : t * (Real.log (p : ℝ) * (v - 2)) = (t * (v - 2)) * Real.log (p : ℝ) := by ring
          rw [this]
          rw [mul_comm (t * (v - 2)) (Real.log (p : ℝ))]
          rw [← Real.rpow_def_of_pos hp_pos']
          have : (p : ℝ) ^ (t * (v - 2)) = (p : ℝ) ^ (t * v) * (p : ℝ) ^ (-2 * t) := by
              rw [← Real.rpow_add hp_pos' (t * v) (-2 * t)]
              congr 1
              ring
          rw [this]
        have h_sum :
          ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
          = (p : ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
          rw [Finset.sum_congr rfl (fun n _ => h_exp_rpow n), ← Finset.sum_mul, mul_comm]
        rw [h_sum, ←mul_assoc, hExp_rpow]
    _ = (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        rw [hExp_rpow]
    _ = (p:ℝ) ^ (-t * (γ + 2)) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
          rw [← Real.rpow_add hp_pos]
          congr 1
          ring
        rw [this]
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (4 * (X + 1)) := by
        apply mul_le_mul_of_nonneg_left hMGF
        apply Real.rpow_nonneg; linarith
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (5 * X) := by
        apply mul_le_mul_of_nonneg_left habsorb
        apply Real.rpow_nonneg; linarith
    _ = 5 * (X : ℝ) * ((p:ℝ) ^ (-t * (γ + 2))) := by ring

end Chernoff

end DkMath.ABC
