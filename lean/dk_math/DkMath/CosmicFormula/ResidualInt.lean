/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- CosmicFormula module: ℤ-based residual and subtractive view

import Mathlib
import DkMath.CosmicFormula.CoreBeamGap

namespace DkMath
namespace CosmicFormula

/--
`big d x u = (x + u)^d`

Big-family の第0層。完成全体を表す（`ℤ` 版）。
-/
def bigInt (d : ℕ) (x u : ℤ) : ℤ :=
  (x + u) ^ d

/--
`gap d x u = u^d`

Big-family の第2層。単位核・余白を表す（`ℤ` 版）。
-/
def gapInt (d : ℕ) (_x u : ℤ) : ℤ :=
  u ^ d

/--
`body d x u = big d x u - gap d x u`

Big-family の第1層。Gap を除いた本体を表す（`ℤ` 版）。
-/
def bodyInt (d : ℕ) (x u : ℤ) : ℤ :=
  bigInt d x u - gapInt d x u

/--
`core d x u = x^d`

Big-family の第3層。Body の主核を表す（`ℤ` 版）。
-/
def coreInt (d : ℕ) (x _u : ℤ) : ℤ :=
  x ^ d

/--
`beam d x u = body d x u - core d x u`

Big-family の第4層。Body から Core を除いた残差を表す（`ℤ` 版）。
-/
def beamInt (d : ℕ) (x u : ℤ) : ℤ :=
  bodyInt d x u - coreInt d x u

/-- 展開確認用。 -/
@[simp] theorem bigInt_def (d : ℕ) (x u : ℤ) :
    bigInt d x u = (x + u) ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem gapInt_def (d : ℕ) (x u : ℤ) :
    gapInt d x u = u ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem bodyInt_def (d : ℕ) (x u : ℤ) :
    bodyInt d x u = bigInt d x u - gapInt d x u := rfl

/-- 展開確認用。 -/
@[simp] theorem coreInt_def (d : ℕ) (x u : ℤ) :
    coreInt d x u = x ^ d := rfl

/-- 展開確認用。 -/
@[simp] theorem beamInt_def (d : ℕ) (x u : ℤ) :
    beamInt d x u = bodyInt d x u - coreInt d x u := rfl

/--
`body + gap = big`

`ℤ` では減算が群演算として扱えるため、仮定なしで戻せる。
-/
theorem bodyInt_add_gapInt_eq_bigInt (d : ℕ) (x u : ℤ) :
    bodyInt d x u + gapInt d x u = bigInt d x u := by
  unfold bodyInt
  exact sub_add_cancel (bigInt d x u) (gapInt d x u)

/--
`beam + core = body`

`ℤ` では仮定なしで `Body = Beam + Core` が復元できる。
-/
theorem beamInt_add_coreInt_eq_bodyInt (d : ℕ) (x u : ℤ) :
    beamInt d x u + coreInt d x u = bodyInt d x u := by
  unfold beamInt
  exact sub_add_cancel (bodyInt d x u) (coreInt d x u)

/--
`core + beam = body`

加法の順序を設計書に合わせた版。
-/
theorem coreInt_add_beamInt_eq_bodyInt (d : ℕ) (x u : ℤ) :
    coreInt d x u + beamInt d x u = bodyInt d x u := by
  rw [add_comm]
  exact beamInt_add_coreInt_eq_bodyInt d x u

/--
`big = body + gap`

設計書の基本関係式（`ℤ` 版）。
-/
theorem bigInt_eq_bodyInt_add_gapInt (d : ℕ) (x u : ℤ) :
    bigInt d x u = bodyInt d x u + gapInt d x u := by
  exact (bodyInt_add_gapInt_eq_bigInt d x u).symm

/--
`big = core + beam + gap`

Big-family 全分解（`ℤ` 版）。
-/
theorem bigInt_eq_coreInt_add_beamInt_add_gapInt (d : ℕ) (x u : ℤ) :
    bigInt d x u = coreInt d x u + beamInt d x u + gapInt d x u := by
  rw [bigInt_eq_bodyInt_add_gapInt]
  rw [coreInt_add_beamInt_eq_bodyInt]

/--
`body = big - gap` の別名として residual を導入するなら、
実際には residual は gap と一致する。
ここでは簡易版として `big - body` を residual と呼ぶ。
-/
def residualInt (d : ℕ) (x u : ℤ) : ℤ :=
  bigInt d x u - bodyInt d x u

/--
`residual = gap`

`body = big - gap` より、残差はちょうど gap に戻る。
-/
theorem residualInt_eq_gapInt (d : ℕ) (x u : ℤ) :
    residualInt d x u = gapInt d x u := by
  unfold residualInt bodyInt
  ring

/-! ## 小さな確認例 -/

/-- `d = 2, x = 3, u = 1` の具体例。 -/
example : bigInt 2 3 1 = 16 := by
  norm_num [bigInt]

example : gapInt 2 3 1 = 1 := by
  norm_num [gapInt]

example : bodyInt 2 3 1 = 15 := by
  norm_num [bodyInt, bigInt, gapInt]

example : coreInt 2 3 1 = 9 := by
  norm_num [coreInt]

example : beamInt 2 3 1 = 6 := by
  norm_num [beamInt, bodyInt, bigInt, gapInt, coreInt]

example : bigInt 2 3 1 = coreInt 2 3 1 + beamInt 2 3 1 + gapInt 2 3 1 := by
  norm_num [bigInt, bodyInt, gapInt, coreInt, beamInt]

/-- 負値を含む `ℤ` 版の確認例。 -/
example : bigInt 3 (-2) 5 = 27 := by
  norm_num [bigInt]

example : gapInt 4 7 (-3) = 81 := by
  norm_num [gapInt]

end CosmicFormula
end DkMath
