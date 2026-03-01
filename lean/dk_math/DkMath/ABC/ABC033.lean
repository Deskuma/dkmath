/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC032

#print "file: DkMath.ABC.ABC033"

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

-- ------------------------------------------------------------------------
-- Final Chernoff - Proofs
-- ------------------------------------------------------------------------

-- ==========================================
-- Chernoff Bound Refactored Design
-- ==========================================
--
-- 4-Layer Architecture:
-- A. Counting (算術・計数) - Already in ABC.lean
-- B. MGF Uniform (解析・MGF) - Parameter t is an argument
-- C. Chernoff Uniform (確率) - Parameter t is an argument
-- D. Explicit Specialization (特殊化) - One-line call to Uniform
-- E. Union Bound (集約) - Uses Uniform directly
--
-- Key Design Principles:
-- 1. t is NOT fixed internally - passed as argument for flexibility
-- 2. Uniform lemmas are the core API - Explicit is just specialization
-- 3. Each layer is independent and replaceable
-- 4. Dependencies flow downward: E → C → B → A

namespace Chernoff


-- ==========================================
-- Common Definitions
-- ==========================================

def Nmul (n : ℕ) : ℕ := Nat.mul n n
def n2a0 (n : ℕ) : ℕ := Nmul n
def n2mul (n : ℕ) : ℕ := 2 * n

example : n2a0 3 = 9 := by rw [n2a0, Nmul, Nat.mul_eq]
example : n2a0 7 = 49 := by rfl
example : n2a0 11 = 121 := by simp [n2a0, Nmul]

def n2a1 (n : ℕ) : ℕ := 2 * n + 1
def n2a2 (n : ℕ) : ℕ := 2 * n + 2
def n2a3' (n : ℕ) : ℕ := 2 * (n + 1) + 1
def n2a3 (n : ℕ) : ℕ := 2 * n + 3

lemma n2a3_to_1 (n : ℕ) : n2a3' n = n2a1 (n + 1) := by rw [n2a3', n2a1]
lemma n2a3_to_2 (n : ℕ) : n2a3' n = n2a2 n + 1 := by rw [n2a3', n2a2]; ring_nf

lemma n2a3_eq (n : ℕ) : n2a3 n = n2a3' n := rfl

lemma n2a1_eq_2 (n : ℕ) : n2a1 n + 1 = n2a2 n := by
  rw [n2a2, n2a1]

example : ∀ n : ℕ, n2a3' n = n2a1 (n + 1) := fun n => n2a3_eq n
example (n : ℕ) : n2a3' n = n2a1 (n + 1) := n2a3_eq n
example (n : ℕ) : n2a3 n = n2a3' n := rfl

example (n : ℕ) : n2a3 n = n2a2 n + 1 := rfl

-- Abbreviation for p-adic valuation of odd numbers
@[simp] abbrev Vp (p n : ℕ) : ℕ := padicValNat p (2 * n + 1)
@[simp] abbrev Vp' (p n : ℕ) : ℕ := padicValNat p (n2a1 n)

lemma Vp_nonneg (p n : ℕ) : 0 ≤ Vp p n := by
  -- padicValNat p n は ℕ 型なので常に 0 以上
  exact Nat.zero_le _

def Vp1 (p n : ℕ) : ℕ := Vp p n

lemma Vp_eq_Vp1 (p n : ℕ) : Vp p n = Vp1 p n := by rfl

-- Excess predicate: v_p(2n+1) > γ
def Excess (p : ℕ) (γ : ℝ) (n : ℕ) : Prop :=
  ((Vp p n : ℤ) : ℝ) - 2 > γ

def Excess' (p : ℕ) (γ : ℝ) (n : ℕ) : Prop :=
  ↑(Int.subNatNat (Vp p n) 2) > γ

example (p : ℕ) (γ : ℝ) (n : ℕ) : Excess p γ n ↔ ((Vp p n : ℤ) : ℝ) - 2 > γ :=
  Iff.rfl

example (p : ℕ) (γ : ℝ) (n : ℕ) : Excess' p γ n ↔ ↑(Int.subNatNat (Vp p n) 2) > γ :=
  Iff.rfl


-- Int.subNatNat の「n < m」の場合の明示的な式変形補題
lemma subNatNat_lt_two_cases (k : ℕ) (hk : ¬k.succ ≥ 2) :
  Int.subNatNat k.succ 2 = ↑k + 1 - 2 := by
  -- k < 2 の場合分け（k = 0 または k = 1）
  cases k
  case zero =>
    -- k = 0 の場合
    -- Int.subNatNat 1 2 = - (2 - 1 : ℤ) = -1
    -- ↑0 + 1 - 2 = 1 - 2 = -1
    rw [Int.subNatNat]
    simp
  case succ k' =>
    -- k = 1 の場合のみ成立（k' = 0）
    have hk' : k' = 0 := by linarith
    rw [hk']
    -- Int.subNatNat 2 2 = ↑(2 - 2) = ↑0 = 0
    simp

-- Int.subNatNat の「n < m」の場合の明示的な式変形補題
lemma subNatNat_lt_two {k : ℕ} (hk : k.succ < 2) : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := by
  -- k.succ < 2 なら k.succ = 1 のみ
  have hk0 : k = 0 := by linarith
  rw [hk0]
  -- Int.subNatNat 1 2 = - (2 - 1 : ℤ) = -1
  rfl

lemma subNatNat_lt_two' {k : ℕ} (hk : ¬k.succ ≥ 2) : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := by
  -- k.succ < 2 なら k.succ = 1 のみ
  have hk0 : k = 0 := by linarith
  rw [hk0]
  -- Int.subNatNat 1 2 = - (2 - 1 : ℤ) = -1
  rfl

-- Int.subNatNat の「n ≥ m」の場合の明示的な式変形補題
lemma subNatNat_ge_two {k : ℕ} : Int.subNatNat k.succ 2 = (k.succ - 2 : ℤ) := by
  -- Int.subNatNat n m = ↑(n - m) when n ≥ m
  rw [Int.subNatNat]
  -- k.succ ≥ 2 なので k.succ - 2 = Nat.sub k.succ 2
  rfl


lemma Excess_iff (p : ℕ) (γ : ℝ) (n : ℕ) :
  Excess p γ n ↔ Excess' p γ n := by
  -- Excess と Excess' の定義はほぼ同じで、型変換の違いのみ
  -- Int.subNatNat (Vp p n) = Vp p n - 2 となる場合とそうでない場合で場合分けする
  simp only [Excess, Excess']
  -- Int.subNatNat の定義により場合分け
  cases h : Vp p n
  case zero =>
    -- Vp p n = 0 の場合
    -- Int.subNatNat 0 2 = -(2 - 0) = -2
    simp [Int.subNatNat]
    -- γ < (0 : ℤ) - 2 ↔ γ < (-2 : ℝ)
    -- γ < Int.subNatNat 0 2 ↔ γ < -2
  case succ k =>
    -- Vp p n = k.succ の場合
    -- k.succ ≥ 2 かどうかで場合分けする
    if hge : k.succ ≥ 2 then
      -- k.succ ≥ 2 の場合
      -- Int.subNatNat k.succ 2 = (k.succ - 2 : ℤ)
      rw [subNatNat_ge_two]
      -- γ < (k.succ : ℤ) - 2 ↔ γ < (k.succ - 2 : ℝ)
      simp
    else
      -- k.succ < 2 の場合（k = 0, k = 1）
      -- Int.subNatNat k.succ 2 = - (2 - k.succ : ℤ) = Int.negSucc (2 - k.succ - 1)
      -- k.succ < 2 の場合は k.succ = 1 のみ
      -- Int.subNatNat 1 2 = - (2 - 1 : ℤ) = -1
      have : Int.subNatNat k.succ 2 = -(2 - k.succ : ℤ) := subNatNat_lt_two' hge
      rw [this]
      -- γ < (k.succ : ℤ) - 2 ↔ γ < - (2 - k.succ : ℝ)
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
        gt_iff_lt, Nat.succ_eq_add_one, neg_sub, Int.cast_sub, Int.cast_ofNat]


-- Note: Decidability is handled by `classical` tactic locally

def pge3 (p : ℕ) : Prop := p ≥ 3
def ple3 (p : ℕ) : Prop := p ≤ 3
def xge3 (X : ℕ) : Prop := X ≥ 3

def const_C : ℕ := 5
def const_K : ℕ := 4
def const_X : ℕ := 100

def C_sub : ℝ := const_C - 1

/-- 素数 p ≥ 3 であるような素数の有限集合を与える関数 -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (2 * n + 2))

/-- p が primesUpTo X に属するための十分条件（p が素数かつ 3 ≤ p かつ p ∣ (2n+1) かつ n ≤ X） -/
lemma prime_mem_primesUpTo_of_dvd_odd {p n X : ℕ} (hnX : n ≤ X) (hp : p.Prime) (hp3 : 3 ≤ p) (hp_dvd : p ∣ (2 * n + 1)) :
  p ∈ primesUpTo X := by
  -- p ≤ 2n+1 ≤ 2X+1 so p < 2X+2 and p ∈ range (2*X+2)
  have h1 : p ≤ 2 * n + 1 := Nat.le_of_dvd (Nat.succ_pos (2 * n)) hp_dvd
  have h2 : 2 * n + 1 ≤ 2 * X + 1 := by nlinarith [hnX]
  have hp_le : p ≤ 2 * X + 1 := le_trans h1 h2
  have hlt : p < 2 * X + 2 := Nat.lt_succ_of_le hp_le
  have hmem : p ∈ Finset.range (2 * X + 2) := Finset.mem_range.mpr hlt
  let H : p ∈ Finset.range (2 * X + 2) ∧ (p.Prime ∧ p ≥ 3) := And.intro hmem (And.intro hp hp3)
  exact Finset.mem_filter.mpr H

lemma prime_mem_primesUpTo_of_dvd_odd' {p n X : ℕ} (hnX : n ≤ X) (hp : p.Prime) (hp3 : 3 ≤ p) (hp_dvd : p ∣ n2a1 n) :
  p ∈ primesUpTo X := by
  -- p ≤ 2n+1 ≤ 2X+1 so p < 2X+2 and p ∈ range (2*X+2)
  have h1 : p ≤ n2a1 n := Nat.le_of_dvd (Nat.succ_pos (2 * n)) hp_dvd
  have h2 : n2a1 n ≤ n2a1 X := by rw [n2a1, n2a1]; nlinarith [hnX]
  have hp_le : p ≤ n2a1 X := le_trans h1 h2
  have hlt : p < n2a2 X := Nat.lt_succ_of_le hp_le
  have hmem : p ∈ Finset.range (n2a2 X) := Finset.mem_range.mpr hlt
  let H : p ∈ Finset.range (n2a2 X) ∧ (p.Prime ∧ p ≥ 3) := And.intro hmem (And.intro hp hp3)
  exact Finset.mem_filter.mpr H

def Vp_sub (p n : ℕ) : ℕ := Vp p (n - 1)  -- padicValNat p (2 * (n - 1) + 1) = padicValNat p (2 * n - 1)
def Vp_add (p n : ℕ) : ℕ := Vp p (n + 1)  -- padicValNat p (2 * n + 3)

example (p n : ℕ) : Vp_sub p n = Vp p (n - 1) := by rw [Vp_sub, Vp]
example (p n : ℕ) : Vp_add p n = Vp p (n + 1) := rfl
-- n > 0 のとき 2 * (n - 1) + 1 = 2 * n - 1 なので padicValNat p (2 * (n - 1) + 1) = padicValNat p (2 * n - 1)
example (p n : ℕ) (hn : n > 0) : Vp_sub p n = padicValNat p (2 * n - 1) := by
  rw [Vp_sub, Vp]
  -- 2 * (n - 1) + 1 = 2 * n - 1 を示す（omega を使わず nat の基本補題で処理）
  rw [two_mul, two_mul]
  have h1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have : (n - 1) + (n - 1) + 1 = (n + n) - 1 := by
    calc (n - 1) + (n - 1) + 1 = (n - 1) + ((n - 1) + 1) := by rw [add_assoc]
      _ = (n - 1) + n := by rw [Nat.sub_add_cancel h1]
      _ = n + (n - 1) := by rw [add_comm]
      _ = (n + n) - 1 := by rw [← Nat.add_sub_assoc h1]
  rw [this]
example (p n : ℕ) (hn : n > 0) : Vp_sub p n = padicValNat p (2 * n - 1) := by
  rw [Vp_sub, Vp]
  -- 2 * (n - 1) + 1 = 2 * n - 1 を示す
  rw [two_mul, two_mul]
  have h : (n - 1 + (n - 1) + 1) = (n + n - 1) := by
    omega
  rw [h]
example (p n : ℕ) : Vp_sub p n = padicValNat p (2 * (n - 1) + 1) := by rw [Vp_sub, Vp]
example (p n : ℕ) : Vp_add p n = padicValNat p (2 *  n + 3)      := rfl
example (p n : ℕ) : Vp_add p n = padicValNat p (n2a3 n) := rfl

-- ==========================================
-- Layer B: MGF Uniform Bound
-- ==========================================
--
-- Goal: ∀ t ∈ (0, log2/log3], MGF ≤ M(p,t)
-- This is extracted from existing layer-cake + telescoping proofs
--
-- NOTE: Detailed proof omitted - use existing mgf_padic_excess_bound_explicit
-- or admit as axiom for rapid prototyping

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

-- ==========================================
-- Chernoff Engine (from Prototype)
-- ==========================================
--
-- Generic engine: from a per-prime MGF bound to a Chernoff tail bound.
-- Assumes: for t ∈ (0, log2/log3],  ∑_{n≤X} p^{t·V_p(n)} ≤ A · (X+1).
-- Then for X ≥ X0 with A·(X+1) ≤ U·X, we get
--   #{n≤X : V_p-2 > γ} ≤ U · X · p^{-t(γ+2)}.

-- ==========================================
-- Markov Inequality
-- ==========================================

-- Markov(指数型)不等式：有限集合上の version（既に完成）
lemma card_filter_le_exp_markov {α}
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
    · simp only [ge_iff_le, h, ↓reduceIte, neg_mul]
      positivity
  have := Finset.sum_le_sum (s := s) (by intro a ha; exact h2 a)
  have : ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
           ≤ Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by
    calc ∑ a ∈ s, (if Z a ≥ γ then (1 : ℝ) else 0)
        ≤ ∑ a ∈ s, Real.exp (-t*γ) * Real.exp (t * Z a) := this
      _ = Real.exp (-t*γ) * ∑ a ∈ s, Real.exp (t * Z a) := by rw [← Finset.mul_sum]
  exact le_trans h1 this


-- Chernoff 不等式（単一素数版、定数 C を明示的に与える版）

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




-- Markov(指数型)不等式：有限集合上の version
-- Auxiliary lemma: t = log2/(2·log3) ≤ log2/log3
lemma t_bound_log2_div_log3 :
    Real.log 2 / (2 * Real.log 3) ≤ Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have : Real.log 3 ≤ 2 * Real.log 3 := by linarith
  exact div_le_div_of_nonneg_left (le_of_lt hlog2) hlog3 this

-- Auxiliary lemma: constant absorption for X ≥ const_X (=100)
lemma absorb_constant_4_to_5 (X : ℕ) (hX : const_X ≤ X) :
    (4 : ℝ) * (X + 1) ≤ const_C * X := by
  have : (4:ℝ) * (↑X + 1) = 4 * ↑X + 4 := by ring
  -- reduce to integer inequality 4 * X + 4 ≤ 5 * X, which is equivalent to 4 ≤ X
  have h4_le_constX : 4 ≤ const_X := by norm_num [const_X]
  have h4_le_X : 4 ≤ X := by linarith [hX, h4_le_constX]
  have h_nat : 4 * X + 4 ≤ const_C * X := by
    rw [const_C]
    -- from 4 ≤ X we get 4*X + 4 ≤ 5*X by linear arithmetic
    linarith
  have h_real : (4 : ℝ) * ↑X + 4 ≤ 5 * ↑X := by exact_mod_cast h_nat
  rw [this]
  exact h_real

end Chernoff

end ABC
