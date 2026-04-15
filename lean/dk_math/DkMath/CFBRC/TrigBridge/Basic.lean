/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

#print "file: DkMath.CFBRC.TrigBridge.Basic"

namespace DkMath.CFBRC.TrigBridge

/-! # CFBRC TrigBridge: Basic Layer

`d=2` の橋

`(a' + x)^2 - x^2 = a'(a' + 2x) = a^2 - x^2`

のうち、純代数的な核を切り出すファイル。
-/

/-- Quadratic Body: `(a' + x)^2 - x^2`. -/
def body2 {α : Type _} [Ring α] (ap x : α) : α :=
  (ap + x) ^ 2 - x ^ 2

/-- CFBRC core polynomial in the complex plane. -/
def cfbrc (d : ℕ) (X Θ : ℂ) : ℂ :=
  (X + Complex.I * Θ) ^ d - (Complex.I * Θ) ^ d

/-- Real-input version of `cfbrc`, coerced into `ℂ`. -/
def cfbrcR (d : ℕ) (X Θ : ℝ) : ℂ :=
  cfbrc d X Θ

/--
二次 Body の因数分解。

`(a' + x)^2 - x^2 = a' * (a' + 2x)` を `CommRing` 上で示す。
-/
lemma body2_factor {α : Type _} [CommRing α] (ap x : α) :
    body2 ap x = ap * (ap + 2 * x) := by
  simp [body2, pow_two]
  ring

/--
`a' = a - x` を代入した Body の再表示。

`body2 (a - x) x = a^2 - x^2` を与える。
これは「Body が消える」のではなく、
二次差の対称形へ書き換わることを表す。
-/
lemma body2_sub {α : Type _} [CommRing α] (a x : α) :
    body2 (a - x) x = a ^ 2 - x ^ 2 := by
  simp [body2, pow_two]

/--
`body2_sub` の因数分解側表示。

`a' = a - x` の下で
`body2 (a - x) x = (a - x) * ((a - x) + 2x)` を返す。
-/
lemma body2_sub_factor {α : Type _} [CommRing α] (a x : α) :
    body2 (a - x) x = (a - x) * ((a - x) + 2 * x) := by
  simpa using (body2_factor (a - x) x)

end DkMath.CFBRC.TrigBridge
