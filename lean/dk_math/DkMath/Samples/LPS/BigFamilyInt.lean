/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- LPS module: Lander, Parkin, and Selfridge conjecture research

import Mathlib

#print "file: DkMath.Samples.LPS.BigFamilyInt"

namespace DkMath
namespace Samples
namespace BigFamilyInt

/--
`big d x u = (x + u)^d`

Big-family の第0層。完成全体を表す（`ℤ` 版）。
-/
def big (d : ℕ) (x u : ℤ) : ℤ :=
  (x + u) ^ d

/--
`gap d x u = u^d`

Big-family の第2層。単位核・余白を表す（`ℤ` 版）。
-/
def gap (d : ℕ) (_x u : ℤ) : ℤ :=
  u ^ d

/--
`body d x u = big d x u - gap d x u`

Big-family の第1層。Gap を除いた本体を表す（`ℤ` 版）。
-/
def body (d : ℕ) (x u : ℤ) : ℤ :=
  big d x u - gap d x u

/--
`core d x u = x^d`

Big-family の第3層。Body の主核を表す（`ℤ` 版）。
-/
def core (d : ℕ) (x _u : ℤ) : ℤ :=
  x ^ d

/--
`beam d x u = body d x u - core d x u`

Big-family の第4層。Body から Core を除いた残差を表す（`ℤ` 版）。
-/
def beam (d : ℕ) (x u : ℤ) : ℤ :=
  body d x u - core d x u

/-- 展開確認用。 -/
@[simp] theorem big_def (d : ℕ) (x u : ℤ) :
    big d x u = (x + u) ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem gap_def (d : ℕ) (x u : ℤ) :
    gap d x u = u ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem body_def (d : ℕ) (x u : ℤ) :
    body d x u = big d x u - gap d x u := rfl

/-- 展開確認用。 -/
@[simp] theorem core_def (d : ℕ) (x u : ℤ) :
    core d x u = x ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem beam_def (d : ℕ) (x u : ℤ) :
    beam d x u = body d x u - core d x u := rfl

/--
`body + gap = big`

`ℤ` では減算が群演算として扱えるため、仮定なしで戻せる。
-/
theorem body_add_gap_eq_big (d : ℕ) (x u : ℤ) :
    body d x u + gap d x u = big d x u := by
  unfold body
  exact sub_add_cancel (big d x u) (gap d x u)

/--
`beam + core = body`

`ℤ` では仮定なしで `Body = Beam + Core` が復元できる。
-/
theorem beam_add_core_eq_body (d : ℕ) (x u : ℤ) :
    beam d x u + core d x u = body d x u := by
  unfold beam
  exact sub_add_cancel (body d x u) (core d x u)

/--
`core + beam = body`

加法の順序を設計書に合わせた版。
-/
theorem core_add_beam_eq_body (d : ℕ) (x u : ℤ) :
    core d x u + beam d x u = body d x u := by
  rw [add_comm]
  exact beam_add_core_eq_body d x u

/--
`big = body + gap`

設計書の基本関係式（`ℤ` 版）。
-/
theorem big_eq_body_add_gap (d : ℕ) (x u : ℤ) :
    big d x u = body d x u + gap d x u := by
  exact (body_add_gap_eq_big d x u).symm

/--
`big = core + beam + gap`

Big-family 全分解（`ℤ` 版）。
-/
theorem big_eq_core_add_beam_add_gap (d : ℕ) (x u : ℤ) :
    big d x u = core d x u + beam d x u + gap d x u := by
  rw [big_eq_body_add_gap]
  rw [core_add_beam_eq_body]

/--
`body = big - gap` の別名として residual を導入するなら、
実際には residual は gap と一致する。
ここでは簡易版として `big - body` を residual と呼ぶ。
-/
def residual (d : ℕ) (x u : ℤ) : ℤ :=
  big d x u - body d x u

/--
`residual = gap`

`body = big - gap` より、残差はちょうど gap に戻る。
-/
theorem residual_eq_gap (d : ℕ) (x u : ℤ) :
    residual d x u = gap d x u := by
  unfold residual body
  ring

/-! ## 小さな確認例 -/

/-- `d = 2, x = 3, u = 1` の具体例。 -/
example : big 2 3 1 = 16 := by
  norm_num [big]

example : gap 2 3 1 = 1 := by
  norm_num [gap]

example : body 2 3 1 = 15 := by
  norm_num [body, big, gap]

example : core 2 3 1 = 9 := by
  norm_num [core]

example : beam 2 3 1 = 6 := by
  norm_num [beam, body, big, gap, core]

example : big 2 3 1 = core 2 3 1 + beam 2 3 1 + gap 2 3 1 := by
  norm_num [big, body, gap, core, beam]

/-- 負値を含む `ℤ` 版の確認例。 -/
example : big 3 (-2) 5 = 27 := by
  norm_num [big]

example : gap 4 7 (-3) = 81 := by
  norm_num [gap]

end BigFamilyInt
end Samples
end DkMath
