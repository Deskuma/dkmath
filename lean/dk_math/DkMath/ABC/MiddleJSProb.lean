/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.JansonPMFProduct

#print "file: DkMath.ABC.MiddleJSProb"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleJansonBridge.lean` から切り出した JSProb owner。
  Janson/Suen middle-band で使う PMF→実数の薄い確率ラッパを置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory
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

/-- jPr_joint is nonnegative (expectation of nonnegative integrand). -/
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

end JSProb

end DkMath.ABC
