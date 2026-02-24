/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- Note: 指数の「次元昇華」原理である無次元宇宙式の量の不変量を Lean で確認する。
-- ここでは自然数版で確認する。実数(CellDim)版は CosmicFormulaCellDim.lean 側で確認する。

import Mathlib

namespace DkMath
namespace CosmicFormulaExp  -- Cosmic Formula Exponent の略

/-!
# 無次元宇宙式（量の不変量）を Lean で確認する

狙い：
- Big_d = (x+u)^d
- Gap_d = u^d
- Body_d = Big_d - Gap_d = (x+u)^d - u^d

さらに無次元比 r = x/u を明示せず（割り算が絡むので）、
代わりに「基本形 x=u」と「指数底 p」への置き換えで一致を確認する。
-/

open Nat

/-- Big の「量」： (x+u)^d -/
def Big (d x u : ℕ) : ℕ := (x + u) ^ d

/-- Gap の「量」： u^d -/
def Gap (d u : ℕ) : ℕ := u ^ d

/-- Body の「量」：Big - Gap -/
def Body (d x u : ℕ) : ℕ := Big d x u - Gap d u

/-- 量の恒等式：Body = (x+u)^d - u^d （定義通り） -/
theorem Body_eq (d x u : ℕ) :
    Body d x u = (x + u)^d - u^d := by
  rfl

/-- 「基本形 x=u」では Body = (2^d - 1) * u^d -/
theorem Body_eq_basic_x_eq_u (d u : ℕ) :
    Body d u u = (2^d - 1) * u^d := by
  -- Body d u u = (u+u)^d - u^d
  -- (u+u)^d = (2*u)^d = (2^d)*(u^d)
  -- だから差は (2^d - 1) * u^d
  unfold Body Big Gap
  -- (u + u) = 2 * u を補題で証明してから rw する
  have h : (u + u) = 2 * u := by rw [two_mul]
  rw [h]
  rw [Nat.mul_pow]
  rw [Nat.sub_mul, one_mul]

/-!
上が環境で詰まる場合があるので、確実版も用意する。
`(2*u)^d = 2^d * u^d` は `Nat.mul_pow` で行ける。
-/

/-- 確実版： (2*u)^d = 2^d * u^d -/
lemma two_mul_pow (d u : ℕ) :
    (2 * u)^d = 2^d * u^d := by
  simp [Nat.mul_pow]

/-- 「基本形 x=u」確実版：Body = (2^d - 1) * u^d -/
theorem Body_eq_basic_x_eq_u' (d u : ℕ) :
    Body d u u = (2^d - 1) * u^d := by
  -- 展開して差をまとめる
  unfold Body Big Gap
  -- (u+u)^d = (2*u)^d
  have h : (u + u)^d = (2 * u)^d := by
    simp [two_mul]
  -- 置換
  simp [h, two_mul_pow, Nat.sub_mul]  -- 環境差があればここは微調整
  -- 場合によって `Nat.sub_mul` が無い/効かないなら、
  -- `Nat.mul_sub_left_distrib` と `Nat.mul_assoc` で手で整形する

/-- 指数底 p を入れた「夢の到達」： Big = (p*u)^d, Gap = u^d, Body = (p^d-1)*u^d -/
theorem Body_eq_base_p (p d u : ℕ) (hp : 1 ≤ p) :
    Body d ((p - 1) * u) u = (p^d - 1) * u^d := by
  -- x = (p-1)u と置けば x+u = pu となる（無次元比 r+1 = p の実装）
  unfold Body Big Gap
  -- x+u = (p-1)u + u = pu
  have hx : ((p - 1) * u + u) = p * u := by
    have h1 : (p - 1) + 1 = p := by
      exact Nat.sub_add_cancel hp
    calc
      (p - 1) * u + u = (p - 1) * u + 1 * u := by
        rw [one_mul]
      _ = ((p - 1) + 1) * u := by
        rw [Nat.add_mul]
      _ = p * u := by
        rw [h1]
  -- 置換して (p*u)^d - u^d を計算し、因数分解する
  rw [hx, Nat.mul_pow]
  -- (p * u)^d - u^d = p^d * u^d - u^d = (p^d - 1) * u^d
  rw [Nat.sub_mul, one_mul]

-- ===== まとめて確認 =========================================================

/-- 量の三点セット：Big, Gap, Body の関係（定義と差分） -/
theorem Big_Gap_Body (d x u : ℕ) :
    Big d x u = (x + u)^d
    ∧ Gap d u = u^d
    ∧ Body d x u = (x + u)^d - u^d := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- 無次元比 (r+1=p) を x=(p-1)u で実現したときの Body 量： (p^d-1)u^d -/
theorem Body_dim_amplify_sub_unit
    (p d u : ℕ) (hp : 1 ≤ p) :
    Body d ((p - 1) * u) u = (p^d - 1) * u^d := by
  simpa using Body_eq_base_p (p := p) (d := d) (u := u) hp


end CosmicFormulaExp
end DkMath
