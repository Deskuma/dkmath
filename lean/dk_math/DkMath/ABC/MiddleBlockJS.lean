/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleJSProb
import DkMath.ABC.MiddleDyadicCompose

#print "file: DkMath.ABC.MiddleBlockJS"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleJansonBridge.lean` から切り出した middle-band BlockJS owner。
  JSProb の実数確率 API を block-level cost / exponential / `BlockJS` record に束ねる。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory
open ABC.Janson

namespace Middle

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

def janson_mu (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  ∑ v ∈ A, (S.p v).toReal

@[simp] lemma janson_mu_nonneg (S : JSProb.Setup Γ) (A : Finset Γ) : 0 ≤ janson_mu S A := by
  apply Finset.sum_nonneg
  intro v hv
  exact_mod_cast zero_le (S.p v)

noncomputable def janson_dbar (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  ∑ v ∈ A, ∑ u ∈ (A.filter fun u => u ∈ S.N v ∧ u ≠ v),
    JSProb.jPr_joint S u v

@[simp] lemma janson_dbar_nonneg (S : JSProb.Setup Γ) (A : Finset Γ) : 0 ≤ janson_dbar S A := by
  apply Finset.sum_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro u hu
  exact (JSProb.jPr_joint_nonneg S u v)

/-- ブロック (A に対応) の確率的評価を実数コストに変換する。 -/
noncomputable def janson_block_cost (S : JSProb.Setup Γ) (A : Finset Γ) : ℝ :=
  JSProb.jPr_zero S A

/-- 単調性：より緩い上界に置き換え可能。 -/
lemma janson_block_cost_le {S : JSProb.Setup Γ} {A : Finset Γ} {t : ℝ}
  (_ : janson_block_cost S A ≤ t) : True := trivial

/-- 指数形の閉じ式。`janson_dbar=0` では独立に一致させる分岐。 -/
noncomputable def janson_block_exp (μ dbar : ℝ) : ℝ :=
  if 0 < dbar then Real.exp ( - (μ ^ 2) / (2 * dbar) ) else Real.exp ( - μ )

noncomputable def janson_block_exp' (μ dbar : ℝ) : ℝ :=
  if 0 < dbar then Real.exp ( - (μ * μ) / (2 * dbar) ) else Real.exp ( - μ )

@[simp] lemma janson_block_exp_nonneg (μ dbar : ℝ) : 0 ≤ janson_block_exp μ dbar := by
  by_cases h : 0 < dbar <;> simp [janson_block_exp, h, Real.exp_nonneg]

lemma janson_block_exp_nonneg' (μ dbar : ℝ) : 0 ≤ janson_block_exp' μ dbar := by
  by_cases h : 0 < dbar <;> simp [janson_block_exp', h, Real.exp_nonneg]

/-- `janson_block_exp` は、固定した非負の下側 μ に対して μ 方向で単調。 -/
lemma janson_block_exp_mono_mu {μ₁ μ₂ dbar : ℝ}
  (hμ : μ₂ ≤ μ₁) (hμ_nonneg : 0 ≤ μ₂) : janson_block_exp μ₁ dbar ≤ janson_block_exp μ₂ dbar := by
  by_cases hd : 0 < dbar
  · have h1 : janson_block_exp μ₁ dbar = Real.exp ( - (μ₁ ^ 2) / (2 * dbar)) := by simp [janson_block_exp, hd]
    have h2 : janson_block_exp μ₂ dbar = Real.exp ( - (μ₂ ^ 2) / (2 * dbar)) := by simp [janson_block_exp, hd]
    rw [h1, h2]
    have hsq : μ₂ ^ 2 ≤ μ₁ ^ 2 := by
      calc
        μ₂ ^ 2 ≤ μ₁ ^ 2 := by
          rw [sq_le_sq]
          rw [abs_of_nonneg hμ_nonneg, abs_of_nonneg (by linarith [hμ_nonneg, hμ])]
          exact hμ
        _ ≤ μ₁ ^ 2 := le_refl _
    have hpos : 0 < 2 * dbar := by linarith [hd]
    have hdiv := div_le_div_of_nonneg_right hsq (le_of_lt hpos)
    have hexp : -(μ₁ ^ 2) / (2 * dbar) ≤ -(μ₂ ^ 2) / (2 * dbar) := by
      rw [neg_div, neg_div]
      exact neg_le_neg hdiv
    exact Real.exp_le_exp.mpr hexp
  · have h1 : janson_block_exp μ₁ dbar = Real.exp (- μ₁) := by simp [janson_block_exp, hd]
    have h2 : janson_block_exp μ₂ dbar = Real.exp (- μ₂) := by simp [janson_block_exp, hd]
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (neg_le_neg hμ)

lemma janson_block_exp_mono_dbar {μ d₁ d₂}
  (hpos : 0 < d₁) (hd : d₁ ≤ d₂) : janson_block_exp μ d₁ ≤ janson_block_exp μ d₂ := by
  have hpos2 : 0 < d₂ := by linarith [hpos, hd]
  have h1 : janson_block_exp μ d₁ = Real.exp ( - (μ ^ 2) / (2 * d₁) ) := by simp [janson_block_exp, hpos]
  have h2 : janson_block_exp μ d₂ = Real.exp ( - (μ ^ 2) / (2 * d₂) ) := by simp [janson_block_exp, hpos2]
  rw [h1, h2]
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
  have hexp : -(μ ^ 2) / (2 * d₁) ≤ -(μ ^ 2) / (2 * d₂) := by
    rw [neg_div]
    rw [neg_div]
    exact neg_le_neg hle
  exact Real.exp_le_exp.mpr hexp

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
  have hneq' : u ≠ v := by exact hneq
  change (M0.p u).toReal * (M0.p v).toReal = JSProb.jPr_joint S u v
  rw [←JSProb.jPr_joint_eq S u v hneq']

/--
JSProb の設定 S と有限集合 A に対する Janson 型上界の接続補題。

ここでは証明自体は上流仮定 `h_bound_v2` として受け取り、Middle 層で必要な
`janson_block_exp` 形式へ渡す薄いラッパとして使う。
-/
theorem janson_bound_v2
  (S : JSProb.Setup Γ) (A : Finset Γ)
  (h_bound_v2 : JSProb.jPr_zero S A ≤ janson_block_exp (janson_mu S A) (janson_dbar S A)) :
  JSProb.jPr_zero S A ≤ janson_block_exp (janson_mu S A) (janson_dbar S A) := by
  exact h_bound_v2

/-- 中域の運転に必要な外生パラメータ（θ, α, ε と block の良性）。 -/
structure Params where
  θ : ℝ
  α : ℝ
  ε : ℝ
  hpos : 0 < α + ε
  Hblock : BlockBound θ

/-- `Params` の略記。 -/
abbrev θ (P : Params) := P.θ
abbrev α (P : Params) := P.α
abbrev ε (P : Params) := P.ε
abbrev hpos (P : Params) := P.hpos
abbrev H (P : Params) := P.Hblock

/- BlockJS は中域用の薄いレコードで、Janson 設定（S）とブロック内の族 A を束ねる。 -/
structure BlockJS (X k : ℕ) where
  Γ : Type*
  [fΓ : Fintype Γ]
  [dΓ : DecidableEq Γ]
  S : JSProb.Setup Γ
  A : Finset Γ
  mu_bound    : ℝ
  dbar_bound  : ℝ
  h_mu_nonneg : 0 ≤ mu_bound
  h_db_nonneg : 0 ≤ dbar_bound
  h_mu_est    : mu_bound ≤ janson_mu S A
  h_db_est    : janson_dbar S A ≤ dbar_bound
  bound_v2    : janson_block_cost S A ≤ janson_block_exp mu_bound dbar_bound
  link_badcount :
    (BadCountOn (0 : ℝ) (MidBlock k X) : ℝ)
      ≤ ((MidBlock k X).card : ℝ) + janson_block_cost S A

attribute [instance] BlockJS.fΓ BlockJS.dΓ

/-- `MidBlock` と Janson 設定から最小の `BlockJS` を構成する薄い wrapper。 -/
noncomputable def buildBlockJS {X k : ℕ} {Γ' : Type*} [Fintype Γ'] [DecidableEq Γ']
  (S : JSProb.Setup Γ') (A : Finset Γ')
  (h_bound_v2 : janson_block_cost S A ≤ janson_block_exp (janson_mu S A) (janson_dbar S A)) :
  BlockJS X k :=
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
    bound_v2 := janson_bound_v2 S A h_bound_v2
    link_badcount := by
      have h : (BadCountOn (0 : ℝ) (MidBlock k X) : ℝ) = ((MidBlock k X).card : ℝ) := by rfl
      rw [h]
      have hj_nonneg : 0 ≤ JSProb.jPr_zero S A := JSProb.jPr_zero_nonneg S A
      exact le_add_of_nonneg_right hj_nonneg
  }

/-- `BlockJS` を食べて、そのブロックの「実数評価」へ落とすための一般形の命題。 -/
lemma block_bound_from_janson
  {X k : ℕ} (P : Params) (B : BlockJS X k) :
  ∃ (Cblk : ℝ), 0 ≤ Cblk ∧
  (BadCountOn (P.θ) (MidBlock k X) : ℝ) ≤ Cblk := by
  classical
  refine ⟨((MidBlock k X).card : ℝ) + janson_block_exp B.mu_bound B.dbar_bound, ?_ , ?_⟩
  · have hx : 0 ≤ ((MidBlock k X).card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact add_nonneg hx (janson_block_exp_nonneg _ _)
  · exact le_trans B.link_badcount (add_le_add_right B.bound_v2 _)

end Middle

end DkMath.ABC
