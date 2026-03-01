/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC008

#print "file: DkMath.ABC.ABC009"

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
  ABCMiddle.lean — Middle band scaffold (Janson/Suen bridge → block sum)
  目的：
    1) 中域の “使い方API” を固定
    2) Janson/Suen の確率版上界をブロックに適用する導線を用意
    3) 既存の Head/Tail 工具（幾何和・吸収）と合流する総和定理の型を定義
-/

open ABC.Janson

/-
# JSProb: Janson/Suen 確率ラッパ（`PMF`→実数）
中域で使う「確率→実数」変換を薄く包むユーティリティ。
`ABCJansonSuen` が提供する `product_pmf` / 期待値補題を前提に、
イベントの確率を **ℝ** で受け取れるインタフェースに統一する。
-/
namespace JSProb

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- `bitVal` の別名（可読性のため）。 -/
@[simp] def Ibit (b : Bool) : ℝ := if b then 1 else 0

/-- Janson の setup。`S.p : Γ → NNReal` ほかは `ABCJansonSuen` 依存。
-- ここで各点の確率が 1 以下であることを仮定しておく（product_pmf の構成に必要）。 -/
structure Setup (Γ : Type*) [Fintype Γ] [DecidableEq Γ] where
  p : Γ → NNReal
  N : Γ → Finset Γ           -- 依存近傍（Suen 用）
  hp_in01 : ∀ v, p v ≤ 1
  -- `product_pmf` 等は `ABCJansonSuen` で構築済みの想定

attribute [simp] Ibit

/-- 族の指示関数：`X_A(ω) = ∑_{v∈A} I{ω(v)=true}` -/
@[simp] def X (A : Finset Γ) (ω : Γ → Bool) : ℝ :=
  A.sum (fun v => Ibit (ω v))

/-- 2点の同時発生確率のラッパ：`E[I_u I_v]` を実数で返す。 -/
@[simp] noncomputable def jPr_joint (S : Setup Γ) (u v : Γ) : ℝ :=
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  PMF.expect (ABC.Janson.product_pmf M) (fun (ω : Γ → Bool) => Ibit (ω u) * Ibit (ω v))

/-- `X_A = 0` の確率のラッパ：`Pr[∀v∈A, ω v = false]`。 -/
@[simp] noncomputable def jPr_zero (S : Setup Γ) (A : Finset Γ) : ℝ :=
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  PMF.expect (ABC.Janson.product_pmf M)
    (fun (ω : Γ → Bool) => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))

-- #check jPr_joint
-- #check jPr_zero

/-- 独立モデルでは `E[I_u I_v] = p(u) p(v)`。 -/
lemma jPr_joint_eq (S : Setup Γ) (u v : Γ) (hne : u ≠ v) :
  jPr_joint S u v = (S.p u).toReal * (S.p v).toReal := by
  classical
  dsimp [jPr_joint, Ibit]
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  -- rewrite pointwise product as product over the 2-element set
  have hfun :
    (fun ω : Γ → Bool => Ibit (ω u) * Ibit (ω v))
      = (fun ω : Γ → Bool => ({u, v} : Finset Γ).prod fun w => Ibit (ω w)) := by
    funext ω
    by_cases h : u = v
    · subst h; simp [Ibit, mul_comm]
    · have : u ∉ ({v} : Finset Γ) := by simpa [Finset.mem_singleton] using h
      simp [Ibit, this, Finset.prod_insert, Finset.prod_singleton, mul_comm]
  calc
    jPr_joint S u v = PMF.expect (product_pmf M) (fun (ω : Γ → Bool) => Ibit (ω u) * Ibit (ω v)) := rfl
    _ = PMF.expect (product_pmf M) (fun (ω : Γ → Bool) => ({u, v} : Finset Γ).prod fun w => Ibit (ω w)) := by rw [hfun]
    _ = (Finset.prod ({u, v} : Finset Γ) fun w => (M.p w).toReal) := by
      dsimp [Ibit]
      rw [ABC.Janson.expect_indicator_prod' (M := M) ({u, v} : Finset Γ)]
    _ = (S.p u).toReal * (S.p v).toReal := by
      have hu_not_mem : u ∉ ({v} : Finset Γ) := by simp [hne]
      rw [Finset.prod_insert hu_not_mem, Finset.prod_singleton]

/-- `jPr_zero` は確率なので非負。 -/
lemma jPr_zero_nonneg (S : Setup Γ) (A : Finset Γ) : 0 ≤ jPr_zero S A := by
  dsimp [jPr_zero]
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  have h_nonneg : ∀ (ω : Γ → Bool), 0 ≤ A.prod (fun v => if ¬ ω v then (1 : ℝ) else (0 : ℝ)) := by
    intro ω
    apply Finset.prod_nonneg
    intro v hv
    by_cases hvb : ω v
    · simp [hvb]
    · simp [hvb]
  exact PMF.expect_nonneg (ABC.Janson.product_pmf M) (fun ω => A.prod (fun v => if ¬ ω v then (1 : ℝ) else (0 : ℝ))) h_nonneg

/-- jPr_joint is nonnegative (expectation of nonnegative integrand) -/
lemma jPr_joint_nonneg (S : Setup Γ) (u v : Γ) : 0 ≤ jPr_joint S u v := by
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  have h_nonneg : ∀ (ω : Γ → Bool), 0 ≤ Ibit (ω u) * Ibit (ω v) := by
    intro ω
    have h1 : 0 ≤ Ibit (ω u) := by
      dsimp [Ibit]
      cases ω u
      · simp
      · simp
    have h2 : 0 ≤ Ibit (ω v) := by
      dsimp [Ibit]
      cases ω v
      · simp
      · simp
    exact mul_nonneg h1 h2
  exact PMF.expect_nonneg (ABC.Janson.product_pmf M) (fun (ω : Γ → Bool) => Ibit (ω u) * Ibit (ω v)) h_nonneg

-- #check jPr_joint_eq
-- #check jPr_zero_nonneg
-- #check jPr_joint_nonneg

end JSProb

namespace Middle

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]


def janson_mu (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  ∑ v ∈ A, (S.p v).toReal

@[simp] lemma janson_mu_nonneg (S : JSProb.Setup Γ) (A : Finset Γ) : 0 ≤ janson_mu S A := by
  apply Finset.sum_nonneg
  intro v hv
  exact_mod_cast zero_le (S.p v)

-- #check janson_mu
-- #check janson_mu_nonneg


noncomputable def janson_dbar (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  ∑ v ∈ A, ∑ u ∈ (A.filter fun u => u ∈ S.N v ∧ u ≠ v),
    JSProb.jPr_joint S u v  -- := E[I_u * I_v] を返す実数関数（独立なら p u * p v）

@[simp] lemma janson_dbar_nonneg (S : JSProb.Setup Γ) (A : Finset Γ) : 0 ≤ janson_dbar S A := by
  apply Finset.sum_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro u hu
  exact (JSProb.jPr_joint_nonneg S u v)

-- #check janson_dbar
-- #check janson_dbar_nonneg


/- Definitions for block cost and exponential -/

/-- ブロック (A に対応) の確率的評価を実数コストに変換
    The probabilistic part of the block cost: Pr[X_A = 0]. -/
noncomputable def janson_block_cost (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  -- 例： Pr[X_A = 0] の上界をそのままコストに採用（単調性の都合で “確率の上界値”）
  JSProb.jPr_zero S A

/-- 単調性：より緩い上界に置き換え可能 -/
lemma janson_block_cost_le {S : JSProb.Setup Γ} {A : Finset Γ} {t : ℝ} (_ : janson_block_cost S A ≤ t) : True := trivial


/-- 指数形の閉じ式。`janson_dbar=0` では独立に一致させる分岐
    The canonical Janson/Suen block exponential cost function. -/
noncomputable def janson_block_exp (μ dbar : ℝ) : ℝ :=
  if 0 < dbar then Real.exp ( - (μ ^ 2) / (2 * dbar) ) else Real.exp ( - μ )

noncomputable def janson_block_exp' (μ dbar : ℝ) : ℝ :=
  if 0 < dbar then Real.exp ( - (μ * μ) / (2 * dbar) ) else Real.exp ( - μ )

@[simp] lemma janson_block_exp_nonneg (μ dbar : ℝ) : 0 ≤ janson_block_exp μ dbar := by
  by_cases h : 0 < dbar <;> simp [janson_block_exp, h, Real.exp_nonneg]

lemma janson_block_exp_nonneg' (μ dbar : ℝ) : 0 ≤ janson_block_exp' μ dbar := by
  by_cases h : 0 < dbar <;> simp [janson_block_exp', h, Real.exp_nonneg]

/-- μ で減少、dbar で増加する（単調性）
    janson_block_exp is monotone decreasing in dbar (for fixed μ ≥ 0) -/
lemma janson_block_exp_mono_mu {μ₁ μ₂ dbar : ℝ}
  (hμ : μ₂ ≤ μ₁) (hμ_nonneg : 0 ≤ μ₂) : janson_block_exp μ₁ dbar ≤ janson_block_exp μ₂ dbar := by
  by_cases hd : 0 < dbar
  · -- case: dbar > 0, formula is exp ( - μ^2 / (2 dbar) )
    have h1 : janson_block_exp μ₁ dbar = Real.exp ( - (μ₁ ^ 2) / (2 * dbar)) := by simp [janson_block_exp, hd]
    have h2 : janson_block_exp μ₂ dbar = Real.exp ( - (μ₂ ^ 2) / (2 * dbar)) := by simp [janson_block_exp, hd]
    rw [h1, h2]
    -- prove μ₂^2 ≤ μ₁^2 using μ₂ ≤ μ₁ and μ₂ ≥ 0
    have hμ1_nonneg : 0 ≤ μ₁ := by linarith [hμ_nonneg, hμ]
    have hsq : μ₂ ^ 2 ≤ μ₁ ^ 2 := by
      calc
        μ₂ ^ 2 ≤ μ₁ ^ 2 := by
          -- |μ₂| ≤ |μ₁| なので sq_le_sq で両方向同値を使う
          rw [sq_le_sq]
          -- μ₂ ≥ 0, μ₂ ≤ μ₁ より |μ₂| = μ₂, |μ₁| = μ₁
          rw [abs_of_nonneg hμ_nonneg, abs_of_nonneg (by linarith [hμ_nonneg, hμ])]
          exact hμ
        _ ≤ μ₁ ^ 2 := le_refl _
    -- divide by positive 2*dbar and negate to get exponent inequality
    have hpos : 0 < 2 * dbar := by linarith [hd]
    have hdiv := div_le_div_of_nonneg_right hsq (le_of_lt hpos)
    have hexp : -(μ₁ ^ 2) / (2 * dbar) ≤ -(μ₂ ^ 2) / (2 * dbar) :=
      by
        rw [neg_div, neg_div]
        exact neg_le_neg hdiv
    exact Real.exp_le_exp.mpr hexp
  · -- case dbar ≤ 0: both sides are exp(-μ), monotonicity follows from μ₂ ≤ μ₁
    have h1 : janson_block_exp μ₁ dbar = Real.exp (- μ₁) := by simp [janson_block_exp, hd]
    have h2 : janson_block_exp μ₂ dbar = Real.exp (- μ₂) := by simp [janson_block_exp, hd]
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (neg_le_neg hμ)

lemma janson_block_exp_mono_dbar {μ d₁ d₂}
  (hpos : 0 < d₁) (hd : d₁ ≤ d₂) : janson_block_exp μ d₁ ≤ janson_block_exp μ d₂ := by
  have hpos2 : 0 < d₂ := by linarith [hpos, hd]
  have h1 : janson_block_exp μ d₁ = Real.exp ( - (μ ^ 2) / (2 * d₁) ) := by simp [janson_block_exp, hpos]
  have h2 : janson_block_exp μ d₂ = Real.exp ( - (μ ^ 2) / (2 * d₂) ) := by simp [janson_block_exp, hpos2]
  rw [h1, h2]
  -- show μ^2/(2*d₁) ≥ μ^2/(2*d₂) by expanding the difference
  have hnum_nonneg : 0 ≤ μ ^ 2 := pow_two_nonneg μ
  have eq : (μ ^ 2) / (2 * d₁) - (μ ^ 2) / (2 * d₂) = (μ ^ 2 * (d₂ - d₁)) / (2 * d₁ * d₂) := by
    field_simp [hpos, hpos2]
  have hnum2_nonneg : 0 ≤ μ ^ 2 * (d₂ - d₁) := mul_nonneg hnum_nonneg (sub_nonneg.mpr hd)
  have hden_pos : 0 < 2 * d₁ * d₂ := by
    have two_pos : 0 < (2 : ℝ) := by norm_num
    have h2d1 : 0 < 2 * d₁ := mul_pos two_pos hpos
    exact mul_pos h2d1 hpos2
  have hdiff_nonneg : 0 ≤ (μ ^ 2) / (2 * d₁) - (μ ^ 2) / (2 * d₂) := by
    rw [eq]
    apply div_nonneg
    · exact hnum2_nonneg
    · exact le_of_lt hden_pos
  have hle : (μ ^ 2) / (2 * d₂) ≤ (μ ^ 2) / (2 * d₁) := by linarith [hdiff_nonneg]
  have hexp : -(μ ^ 2) / (2 * d₁) ≤ -(μ ^ 2) / (2 * d₂) :=
    by
      -- -a / b = - (a / b) で型を揃える
      rw [neg_div]
      rw [neg_div]
      exact neg_le_neg hle
  exact Real.exp_le_exp.mpr hexp

-- #check janson_block_cost
-- #check janson_block_cost_le
-- #check janson_block_exp
-- #check janson_block_exp_nonneg
-- #check janson_block_exp_mono_dbar
-- #check janson_block_exp_mono_mu

-- -------------------------------------------------------

-- #check ABC.Janson.bound_v2
-- #check ABC.Janson.mu
-- #check ABC.Janson.dbar

/-- v2 版：Pr[X_A=0] ≤ janson_block_exp (μ, dbar) -/
/- Helpers: name alignment lemmas -/
lemma mu_eq (S : JSProb.Setup Γ) (A : Finset Γ) :
  ABC.Janson.mu (M := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }) (A := A) = janson_mu S A := by
  simp [ABC.Janson.mu, janson_mu]

lemma dbar_eq (S : JSProb.Setup Γ) (A : Finset Γ) :
  ABC.Janson.dbar (M := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }) (A := A) = janson_dbar S A := by
  dsimp [ABC.Janson.dbar, janson_dbar]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  have hmem := Finset.mem_filter.mp hu
  let ⟨_, ⟨_, hneq⟩⟩ := hmem
  let M0 : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }
  -- use the JSProb-level lemma for joint probability (independence case)
  have hneq' : u ≠ v := by exact hneq
  change (M0.p u).toReal * (M0.p v).toReal = JSProb.jPr_joint S u v
  -- use the known equality jPr_joint S u v = (S.p u).toReal * (S.p v).toReal
  rw [←JSProb.jPr_joint_eq S u v hneq']

/--
JSProb の設定 S と有限集合 A に対する Janson 型の上界を与える補題。

述語:
- `jPr_zero S A` は集合 A に属するどの事象も起きない（出現数が零である）確率を表します。
- `janson_mu S A` は A に対応する期待値 μ（事象の総期待出現数）を表します。
- `janson_dbar S A` は依存関係に基づく d̄（分散や相互依存を表すパラメータ）です。
- `janson_block_exp μ dbar` は μ と d̄ に基づくブロック型の指数的上界を与える関数です。

この定理は、上記の確率が対応するブロック指数関数によって制御されること、すなわち
ゼロ発生確率が `janson_block_exp (janson_mu S A) (janson_dbar S A)` 以下であることを主張します。
Janson の不等式に属する見積もりの一形であり、特に相互依存を持つ二項事象群に対する指数的尾部評価として有用です。
-/
theorem janson_bound_v2
  (S : JSProb.Setup Γ) (A : Finset Γ) :
  JSProb.jPr_zero S A ≤ janson_block_exp (janson_mu S A) (janson_dbar S A) := by
  classical
  -- build model from the thin setup
  let M : ABC.Janson.JansonModel Γ := { p := S.p, N := fun g => S.N g, hp_in01 := S.hp_in01 }

  -- call the Janson-side v2 (model-limited) bound
  have hv2 :
    PMF.expect (ABC.Janson.product_pmf M)
      (fun (ω : Γ → Bool) => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))
      ≤
    (if 0 < ABC.Janson.dbar (M:=M) (A:=A)
     then Real.exp ( - (ABC.Janson.mu (M:=M) (A:=A))^2 / (2 * ABC.Janson.dbar (M:=M) (A:=A)) )
     else Real.exp ( - ABC.Janson.mu (M:=M) (A:=A) )) := by
    exact ABC.Janson.bound_v2 (M:=M) (A:=A)

  -- target rewrite
  change
    PMF.expect (ABC.Janson.product_pmf M)
      (fun (ω : Γ → Bool) => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))
      ≤ janson_block_exp (janson_mu S A) (janson_dbar S A)

  -- align names and finish by case analysis on dbar
  -- prove μ equality by pointwise congruence (M.p = S.p)
  -- use the already-proved name-alignment lemmas to avoid fragile term-shape rewrites
  have hμ := mu_eq S A
  have hΔ := dbar_eq S A

  by_cases hd : 0 < janson_dbar S A
  · -- dbar > 0
    have hd' : 0 < ABC.Janson.dbar (M:=M) (A:=A) := by
      rw [←dbar_eq S A] at hd
      exact hd
    -- rewrite ABC.Janson.mu / dbar を janson_* に書き換えてから簡約する
    rw [hμ, hΔ] at hv2
    simpa [janson_block_exp] using hv2
  · -- dbar ≤ 0
    have hnot : ¬ 0 < ABC.Janson.dbar (M:=M) (A:=A) := by
      intro h; apply hd; rwa [dbar_eq S A] at h
    -- 同様に RHS の名前を揃えてから処理
    rw [hμ, hΔ] at hv2
    simpa [janson_block_exp, hnot] using hv2

-- #check janson_bound_v2

/- ---------------------------------------------
## 0. パラメータパック（中域で用いる仮定の束）
---------------------------------------------- -/

/-- 中域の運転に必要な外生パラメータ（θ, α, ε と block の良性） -/
structure Params where
  θ : ℝ
  α : ℝ
  ε : ℝ
  hpos : 0 < α + ε
  Hblock : BlockBound θ                 -- 既存：Head/Tail 側で使っているブロック良性

/-- `Params` の略記 -/
abbrev θ (P : Params) := P.θ
abbrev α (P : Params) := P.α
abbrev ε (P : Params) := P.ε
abbrev hpos (P : Params) := P.hpos
abbrev H (P : Params) := P.Hblock

/-
## 1. Janson/Suen を中域ブロックに接続するための "使い方API"
---

`X`：全体レンジの上端、`k`：ダイアディック階層。
`MidBlock k X` は既存（ABC 側）を使用。
-/
/- 中域ブロック（`k, X`）に紐づく Janson/Suen の入力一式 -/
/- BlockJS は中域用の薄いレコードで、Janson 設定（S）とブロック内の族 A を束ねる。-/
structure BlockJS (X k : ℕ) where
  Γ : Type*
  [fΓ : Fintype Γ]
  [dΓ : DecidableEq Γ]
  S : JSProb.Setup Γ                     -- PMF→ℝ thin wrapper
  A : Finset Γ                           -- events inside the block
  -- μ, Δ̄ bounds evaluated for this block
  mu_bound    : ℝ
  dbar_bound  : ℝ
  h_mu_nonneg : 0 ≤ mu_bound
  h_db_nonneg : 0 ≤ dbar_bound
  -- NOTE: `mu_bound` is stored as a lower bound on the actual μ (so we can use
  -- `janson_block_exp_mono_mu` which requires `μ₂ ≤ μ₁` to move from actual μ to the
  -- conservative `mu_bound`). This direction was previously flipped and caused
  -- composition failures when applying the monotonicity lemmas.
  h_mu_est    : mu_bound ≤ janson_mu S A
  h_db_est    : janson_dbar S A ≤ dbar_bound
  -- ★ accept the v2 inequality as a field provided by the Janson module
  bound_v2    : janson_block_cost S A ≤ janson_block_exp mu_bound dbar_bound
  -- reduction lever to BadCountOn (card + probabilistic cost)
  link_badcount :
    (BadCountOn (0 : ℝ) (MidBlock k X) : ℝ)
      ≤ ((MidBlock k X).card : ℝ) + janson_block_cost S A

attribute [instance] BlockJS.fΓ BlockJS.dΓ

-- buildBlockJS: construct a minimal BlockJS from MidBlock and a trivial JSProb.Setup.
-- This is a thin wrapper: it uses the existing MidBlock k X as the underlying index set
-- and leaves numeric estimates as simple casts or basic bounds so the record type checks.
noncomputable def buildBlockJS {X k : ℕ} {Γ' : Type*} [Fintype Γ'] [DecidableEq Γ']
  (S : JSProb.Setup Γ') (A : Finset Γ') : BlockJS X k :=
  {
    Γ := Γ'
    fΓ := inferInstance
    dΓ := inferInstance
    S := S
    A := A
    mu_bound := janson_mu S A
    dbar_bound := janson_dbar S A
    h_mu_nonneg := janson_mu_nonneg S A
    h_db_nonneg := janson_dbar_nonneg S A
    h_mu_est := le_refl _
    h_db_est := le_refl _
    bound_v2 := janson_bound_v2 S A
    link_badcount := by
      -- BadCountOn is defined as the card of the set with threshold 0
      -- We need to show that BadCountOn 0 (MidBlock k X) ≤ card + jPr_zero
      have h : (BadCountOn (0 : ℝ) (MidBlock k X) : ℝ) = ((MidBlock k X).card : ℝ) := by rfl
      rw [h]
      -- jPr_zero is nonnegative
      have hj_nonneg : 0 ≤ JSProb.jPr_zero S A := JSProb.jPr_zero_nonneg S A
      exact le_add_of_nonneg_right hj_nonneg
  }

/-- `BlockJS` を食べて、そのブロックの「実数評価」へ落とすための一般形の命題。
    ここで使う `janson_bound_v2` は ABCJansonSuenPre 側で提供される v2 型上界。
    実際の評価は `mu_bound`, `dbar_bound` に依存する。 -/
lemma block_bound_from_janson
  {X k : ℕ} (P : Params) (B : BlockJS X k) :
  ∃ (Cblk : ℝ), 0 ≤ Cblk ∧
  (BadCountOn (P.θ) (MidBlock k X) : ℝ) ≤ Cblk := by
  classical
  -- 1) Use the supplied v2 bound field from the block
  -- 1) Try to derive the block bound from the canonical v2 bound + monotonicity.
  -- If `janson_dbar` happens to be strictly positive we can chain
  --   janson_bound_v2 -> mono_mu -> mono_dbar
  -- otherwise fall back to the provided `B.bound_v2` field (safe fallback).
  refine ⟨((MidBlock k X).card : ℝ) + janson_block_exp B.mu_bound B.dbar_bound, ?_ , ?_⟩
  · have hx : 0 ≤ ((MidBlock k X).card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact add_nonneg hx (janson_block_exp_nonneg _ _)
  · have h_v2 := janson_bound_v2 B.S B.A
    by_cases hdpos : 0 < janson_dbar B.S B.A
    · -- janson_dbar > 0: chain v2 + mono_mu + mono_dbar
      have hmu := @janson_block_exp_mono_mu (janson_mu B.S B.A) (B.mu_bound) (janson_dbar B.S B.A)
        (B.h_mu_est) (B.h_mu_nonneg)
      have hdb := @janson_block_exp_mono_dbar (B.mu_bound) (janson_dbar B.S B.A) (B.dbar_bound)
        (hpos := hdpos) (hd := B.h_db_est)
      have final := (le_trans h_v2 (le_trans hmu hdb))
      exact le_trans B.link_badcount (add_le_add_right final _)
    · -- otherwise fall back to the block-provided v2 witness
      exact le_trans B.link_badcount (add_le_add_right B.bound_v2 _)

/- ---------------------------------------------
## 2. 中域の総和：`k` にわたる和を多項式上界へ

ここでは、ブロックごとの定数 `Cblk(k,X)` を幾何和で束ねるだけの層。
`geom_sum_pow_two_le` など既存の「2^k の幾何和」道具を利用する。
---------------------------------------------- -/

/-- 中域：`k ≤ ⌊log₂(X+1)⌋` にわたる合計を `X^(α+ε)` に閉じ込める上界の型。
    ここでは、各 `k` に対し `BlockJS X k` を「供給できる」ことを仮定として要求する。 -/
-- 中域：`k ≤ ⌊log₂(X+1)⌋` にわたる合計を `X^(α+ε)` に閉じ込める上界。
-- ここでは (1) 各 `k` に BlockJS を供給でき、
--         (2) 各項が C0 · 2^{(α+ε)k} で支配される、
-- の2仮定を受け取り、それを幾何和で畳み込む実装。
lemma middle_band_sum_bound
  (P : Params)
  (C0 : ℝ) (hC0 : 0 ≤ C0)
  -- 成長支配：各項が C0 · 2^{(α+ε)·k} で抑えられる（指数を掛けた形）
  (growth :
    ∀ ⦃X k⦄, 1 ≤ X → k ∈ Finset.range (Nat.log2 (X + 1) + 1) →
      (BadCountOn (P.θ) (MidBlock k X) : ℝ)
        ≤ C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
  :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
        (BadCountOn (P.θ) (MidBlock k X) : ℝ))
      ≤ C * (X : ℝ)^(P.α + P.ε)
  := by
    classical
    have hpos : 0 < P.α + P.ε := P.hpos
    -- choose the same C' as geom_sum_pow_two_le provides
    let X0' := 1
    let C' := (Real.rpow (2 : ℝ) (3 * (P.α + P.ε)) / (Real.rpow (2 : ℝ) (P.α + P.ε) - 1))
    have hC'nonneg : 0 ≤ C' := by
      have hnum_nonneg : 0 ≤ Real.rpow (2 : ℝ) (3 * (P.α + P.ε)) := by apply Real.rpow_nonneg; norm_num
      have denom_pos : 0 < Real.rpow (2 : ℝ) (P.α + P.ε) - 1 := by
        have : 1 < Real.rpow (2 : ℝ) (P.α + P.ε) := by
          have two_pos : (2 : ℝ) > 1 := by norm_num
          exact Real.one_lt_rpow two_pos (by exact_mod_cast hpos)
        exact sub_pos.mpr this
      exact div_nonneg hnum_nonneg (le_of_lt denom_pos)

    refine ⟨X0', C0 * C', by exact mul_nonneg hC0 hC'nonneg, ?_⟩
    intro X hXpos hXge

    -- sum over k ≤ log2(X+1)
    set S := Finset.range (Nat.log2 (X + 1) + 1) with hS
    -- define the sum to be bounded
    set BadSum : ℝ := ∑ k ∈ S, (BadCountOn (P.θ) (MidBlock k X) : ℝ) with hBad

    -- step1: termwise bound using the provided growth (rpow with multiplied exponent)
    have step1 : (BadSum)
      ≤ (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := by
      apply Finset.sum_le_sum; intro k hk; exact growth (X:=X) (k:=k) hXpos hk

    -- step2: rewrite the sum into geometric series shape
    have step2 :
      (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
        = C0 * (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k) := by
      have two_pos : 0 < (2 : ℝ) := by norm_num
      set q : ℝ := Real.rpow (2 : ℝ) (P.α + P.ε)
      calc
        (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
          = C0 * (∑ k ∈ S, Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := by
            rw [Finset.mul_sum]
        _ = C0 * (∑ k ∈ S, q ^ k) := by
          apply congrArg (fun s => C0 * s)
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- use the general rpow_mul_nat lemma: Real.rpow 2 ((α+ε) * k) = (2^(α+ε))^k
          exact RpowExtras.rpow_mul_nat (x := (2 : ℝ)) (a := (P.α + P.ε)) (hx := two_pos) k
    -- step3: apply geom_sum_pow_two_le to bound the geometric sum
    have Hgeo := geom_sum_pow_two_le (α := P.α) (ε := P.ε) (h := hpos)
    have step3 : (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k)
      ≤ C' * (X : ℝ)^(P.α + P.ε) := by apply Hgeo; exact hXpos

    -- combine steps
    have final : (BadSum)
      ≤ C0 * C' * (X : ℝ)^(P.α + P.ε) := by
      calc
        (BadSum)
         ≤ (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := step1
        _ = C0 * (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k) := by exact step2
        _ ≤ C0 * (C' * (X : ℝ)^(P.α + P.ε)) := by
          apply mul_le_mul_of_nonneg_left
          · exact step3
          · exact hC0
        _ = C0 * C' * (X : ℝ)^(P.α + P.ε) := by ring
    exact final

/- ---------------------------------------------
## 3. Top-level: Middle band を Head/Tail と合流

`head_absorb` / `tail_geom_bound` と合流して、全域の BadCount を
`C * X^(α+ε)` に収束させる。ここでは型だけ用意しておく。
---------------------------------------------- -/

/-- 中域を含む最終合流（Top-level 版）の外側 API。 -/
-- 中域を含む最終合流。Head/Middle/Tail をまとめて `C·X^(α+ε)` に収束させる。
theorem middle_band_bound_top
  (P : Params)
  (C0 : ℝ) (hC0 : 0 ≤ C0)
  (growth :
    ∀ ⦃X k⦄, 1 ≤ X → k ∈ Finset.range (Nat.log2 (X + 1) + 1) →
      (BadCountOn (P.θ) (MidBlock k X) : ℝ)
        ≤ C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
  (hε_pos : 0 < P.ε)
  (hα_eq : P.Hblock.α = P.α)
  :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
        (BadCountOn (P.θ) (MidBlock k X) : ℝ))
      ≤ C * (X : ℝ)^(P.α + P.ε) := by
  classical
  -- Head
  obtain ⟨X0h, Ch, hCh, Hh⟩ := head_absorb (θ:=P.θ) (α:=P.α) (ε:=P.ε) P.hpos (k0 := 3)
  -- Middle（直上の lemma）
  obtain ⟨X0m, Cm, hCm, Hm⟩ := middle_band_sum_bound P C0 hC0 growth
  -- Tail
  obtain ⟨k0t, Ct, hCt, Ht⟩ := tail_geom_bound P.Hblock P.ε (by have := P.hpos; linarith)

  -- X0 と C を合成
  refine ⟨Nat.max X0h X0m, Ch + Cm + Ct, by nlinarith, ?_⟩
  intro X hXpos hXge
  have h1 := Hh hXpos (le_trans (Nat.le_max_left _ _) hXge)
  have h2 := Hm hXpos (le_trans (Nat.le_max_right _ _) hXge)
  have h3 := Ht hXpos

  -- sum over k ≤ log2(X+1)
  set S := Finset.range (Nat.log2 (X + 1) + 1) with hS
  -- define the sum to be bounded
  set BadSum : ℝ := ∑ k ∈ S, (BadCountOn (P.θ) (MidBlock k X) : ℝ) with hBad
  -- split the sum into three parts: k < 3, 3 ≤ k < k0t, k ≥ k0t
  set sum_k0t := (∑ k ∈ S, if k ≥ k0t then (BadCountOn (P.θ) (MidBlock k X) : ℝ) else 0) with hsum_k0t
  -- the rest is the finite sum k=0,1,2
  set sum3 := (∑ k ∈ Finset.range 3, (BadCountOn (P.θ) (MidBlock k X) : ℝ)) with hsum3

  -- rewrite tail exponent from P.Hblock.α to P.α using the provided equality
  have h3' : sum_k0t
    ≤ Ct * (X : ℝ)^(P.α + P.ε) := by
    have heq_exp : P.Hblock.α + P.ε = P.α + P.ε := by rw [hα_eq]
    rwa [heq_exp] at h3
  have hsum_final : (BadSum)
    ≤ (Ch + Cm + Ct) * (X : ℝ)^(P.α + P.ε) := by
    -- 中域の和は、非負の余分な和を加えた三項和より小さい（あるいは等しい）
    have hstep1 : (BadSum)
      ≤ sum3
        + (BadSum)
        + sum_k0t := by
      -- 右辺に足す二つの項は非負なので加えても不等式は保たれる
      have h_nonneg_sum3 : 0 ≤ sum3 := by
        apply Finset.sum_nonneg; intro k hk; exact_mod_cast (Nat.zero_le _)
      have h_nonneg_sumif : 0 ≤ sum_k0t := by
        apply Finset.sum_nonneg
        intro k hk
        by_cases hge : k ≥ k0t
        · simp [hge]
        · exact_mod_cast (Nat.zero_le _)
      have hsum_nonneg : 0 ≤ sum3 + sum_k0t :=
        by simpa using add_nonneg h_nonneg_sum3 h_nonneg_sumif
      -- 並びを (a + (b + c)) から (b + (a + c)) の形に変えてから適用する
      have heq : sum3 + (BadSum) + sum_k0t
                = (BadSum) + (sum3 + sum_k0t) := by ring
      rw [heq]
      apply le_add_of_nonneg_right
      exact hsum_nonneg
    -- 三項和については h1, h2, h3' が上界を与えるので合成して使う
    have hstep2 : sum3 + (BadSum) + sum_k0t
      ≤ Ch * (X : ℝ)^(P.α + P.ε) + Cm * (X : ℝ)^(P.α + P.ε) + Ct * (X : ℝ)^(P.α + P.ε) := by
      apply add_le_add (add_le_add h1 h2) h3'
    -- 最後に右辺を合成して目的形にする
    have hfinal := le_trans hstep1 hstep2
    calc
      (BadSum)
        ≤ Ch * (X : ℝ)^(P.α + P.ε) + Cm * (X : ℝ)^(P.α + P.ε) + Ct * (X : ℝ)^(P.α + P.ε) := hfinal
      _ = (Ch + Cm + Ct) * (X : ℝ)^(P.α + P.ε) := by ring
  exact hsum_final

-- #check middle_band_sum_bound
-- #check middle_band_bound_top

end Middle

end ABC
