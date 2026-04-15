/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Trig
import DkMath.CFBRC.TrigBridge.Complex
import DkMath.CFBRC.TrigBridge.General

#print "file: DkMath.CFBRC.TrigBridge.Main"

namespace DkMath.CFBRC.TrigBridge

/-! # CFBRC TrigBridge: Main Theorems

代数層・三角層・複素層を束ね、`d=2` の橋

`(a' + x)^2 - x^2 = a'(a' + 2x) = a^2 cos^2 φ = Re G_2(a cos φ, a sin φ)`

を Lean 定理として固定する。
-/

/--
general 再帰補題から導く `d=2` 実部明示式。

`cfbrcRe 2 X Θ = X^2`。
-/
lemma cfbrcRe_two_from_general (X Θ : ℝ) :
    cfbrcRe 2 X Θ = X ^ 2 := by
  calc
    cfbrcRe 2 X Θ =
        X * cfbrcRe 1 X Θ - Θ * cfbrcIm 1 X Θ + X * Complex.re ((Complex.I * Θ) ^ 1) := by
          simpa using cfbrcRe_succ' (d := 1) X Θ
    _ = X * X - Θ * 0 + X * 0 := by
          simp
    _ = X ^ 2 := by
          ring

/--
general 再帰補題から導く `d=2` 虚部明示式。

`cfbrcIm 2 X Θ = 2XΘ`。
-/
lemma cfbrcIm_two_from_general (X Θ : ℝ) :
    cfbrcIm 2 X Θ = 2 * X * Θ := by
  calc
    cfbrcIm 2 X Θ =
        X * cfbrcIm 1 X Θ + Θ * cfbrcRe 1 X Θ + X * Complex.im ((Complex.I * Θ) ^ 1) := by
          simpa using cfbrcIm_succ' (d := 1) X Θ
    _ = X * 0 + Θ * X + X * Θ := by
          simp
    _ = 2 * X * Θ := by
          ring

/--
`d=2` 実部公式を general 補題系から再導出した形。

`Complex.lean` の `cfbrc_two_re` と同じ主張を、
`General.lean` の `cfbrcRe_succ'` から得る。
-/
theorem cfbrc_two_re_via_general (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 := by
  simpa [cfbrcRe] using cfbrcRe_two_from_general X Θ

/--
`d=2` 虚部公式を general 補題系から再導出した形。

`Complex.lean` の `cfbrc_two_im` と同じ主張を、
`General.lean` の `cfbrcIm_succ'` から得る。
-/
theorem cfbrc_two_im_via_general (X Θ : ℝ) :
    Complex.im (cfbrcR 2 X Θ) = 2 * X * Θ := by
  simpa [cfbrcIm] using cfbrcIm_two_from_general X Θ

/--
極座標代入後の `d=2` 実部（general 補題由来）。

`Re (cfbrcR 2 (a cos φ) (a sin φ)) = a^2 cos^2 φ`。
-/
theorem cfbrc_two_re_polar_via_general (a φ : ℝ) :
    Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) = a ^ 2 * (Real.cos φ) ^ 2 := by
  rw [cfbrc_two_re_via_general]
  ring

/--
極座標代入後の `d=2` 虚部（general 補題由来）。

`Im (cfbrcR 2 (a cos φ) (a sin φ)) = 2 a^2 sin φ cos φ`。
-/
theorem cfbrc_two_im_polar_via_general (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ := by
  rw [cfbrc_two_im_via_general]
  ring

/--
Body 形と CFBRC 実部の同一化（`d=2`）。

`body2 (a*(1-sin φ)) (a*sin φ) = Re(cfbrcR 2 (a cos φ) (a sin φ))`。
-/
theorem body2_eq_re_cfbrc2 (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_trig, cfbrc_two_re_polar_via_general]

/--
因数分解形と CFBRC 実部の同一化（`d=2`）。

`(a*(1-sin φ))*((a*(1-sin φ)) + 2*(a*sin φ)) = Re(cfbrcR 2 (a cos φ) (a sin φ))`。
-/
theorem factor_eq_re_cfbrc2 (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ)) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_factor_trig, cfbrc_two_re_polar_via_general]

end DkMath.CFBRC.TrigBridge
