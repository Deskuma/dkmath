/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Basic
import Mathlib.Tactic

namespace DkMath.CFBRC.TrigBridge

noncomputable section

/-! # CFBRC TrigBridge: General `d` Helpers

このファイルは `cfbrcR d X Θ = (X + iΘ)^d - (iΘ)^d` の
実部・虚部を一般 `d` で追跡するための補助補題群を提供する。

`d=2` の明示式は `Complex.lean` に固定済みで、
ここでは general `d` 拡張時に使う再帰形を先に用意する。
-/

/-- General `d` の CFBRC 実部を切り出した補助定義。 -/
def cfbrcRe (d : ℕ) (X Θ : ℝ) : ℝ :=
  Complex.re (cfbrcR d X Θ)

/-- General `d` の CFBRC 虚部を切り出した補助定義。 -/
def cfbrcIm (d : ℕ) (X Θ : ℝ) : ℝ :=
  Complex.im (cfbrcR d X Θ)

/-- 基底値: `d=0` の CFBRC 実部は 0。 -/
@[simp] lemma cfbrcRe_zero (X Θ : ℝ) : cfbrcRe 0 X Θ = 0 := by
  simp [cfbrcRe, cfbrcR, cfbrc]

/-- 基底値: `d=0` の CFBRC 虚部は 0。 -/
@[simp] lemma cfbrcIm_zero (X Θ : ℝ) : cfbrcIm 0 X Θ = 0 := by
  simp [cfbrcIm, cfbrcR, cfbrc]

/-- 基底値: `d=1` の CFBRC 実部は `X`。 -/
@[simp] lemma cfbrcRe_one (X Θ : ℝ) : cfbrcRe 1 X Θ = X := by
  simp [cfbrcRe, cfbrcR, cfbrc]

/-- 基底値: `d=1` の CFBRC 虚部は 0。 -/
@[simp] lemma cfbrcIm_one (X Θ : ℝ) : cfbrcIm 1 X Θ = 0 := by
  simp [cfbrcIm, cfbrcR, cfbrc]

/--
`d -> d+1` の分解公式。

`A := X + iΘ`, `B := iΘ` とおくと
`A^(d+1) - B^(d+1) = A*(A^d-B^d) + (A-B)*B^d`。
ここで `A-B = X`（実数埋め込み）なので、右辺第2項は `X * (iΘ)^d` になる。
-/
lemma cfbrcR_succ_decompose (d : ℕ) (X Θ : ℝ) :
    cfbrcR (d + 1) X Θ =
      (X + Complex.I * Θ) * cfbrcR d X Θ + X * (Complex.I * Θ) ^ d := by
  simp [cfbrcR, cfbrc, pow_succ, sub_eq_add_neg]
  ring

/--
一般 `d` の実部再帰式。

`cfbrcR_succ_decompose` に `Complex.mul_re` を適用した形で、
`Re (cfbrcR (d+1))` を `Re/Im (cfbrcR d)` と `(iΘ)^d` の実部で表す。
-/
lemma cfbrcRe_succ (d : ℕ) (X Θ : ℝ) :
    Complex.re (cfbrcR (d + 1) X Θ) =
      X * Complex.re (cfbrcR d X Θ) - Θ * Complex.im (cfbrcR d X Θ) +
        X * Complex.re ((Complex.I * Θ) ^ d) := by
  rw [cfbrcR_succ_decompose, Complex.add_re]
  rw [Complex.mul_re]
  simp [sub_eq_add_neg]

/--
一般 `d` の虚部再帰式。

`cfbrcR_succ_decompose` に `Complex.mul_im` を適用した形で、
`Im (cfbrcR (d+1))` を `Re/Im (cfbrcR d)` と `(iΘ)^d` の虚部で表す。
-/
lemma cfbrcIm_succ (d : ℕ) (X Θ : ℝ) :
    Complex.im (cfbrcR (d + 1) X Θ) =
      X * Complex.im (cfbrcR d X Θ) + Θ * Complex.re (cfbrcR d X Θ) +
        X * Complex.im ((Complex.I * Θ) ^ d) := by
  rw [cfbrcR_succ_decompose, Complex.add_im]
  rw [Complex.mul_im]
  simp

/--
`cfbrcRe` 補助定義を使った実部再帰式（`cfbrcRe_succ` の別表現）。
-/
lemma cfbrcRe_succ' (d : ℕ) (X Θ : ℝ) :
    cfbrcRe (d + 1) X Θ =
      X * cfbrcRe d X Θ - Θ * cfbrcIm d X Θ + X * Complex.re ((Complex.I * Θ) ^ d) := by
  simpa [cfbrcRe, cfbrcIm] using cfbrcRe_succ d X Θ

/--
`cfbrcIm` 補助定義を使った虚部再帰式（`cfbrcIm_succ` の別表現）。
-/
lemma cfbrcIm_succ' (d : ℕ) (X Θ : ℝ) :
    cfbrcIm (d + 1) X Θ =
      X * cfbrcIm d X Θ + Θ * cfbrcRe d X Θ + X * Complex.im ((Complex.I * Θ) ^ d) := by
  simpa [cfbrcRe, cfbrcIm] using cfbrcIm_succ d X Θ

/--
`(iΘ)^2` の実部評価。

`Re((iΘ)^2) = -Θ^2`。
-/
lemma pure_phase_sq_re (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ 2) = -(Θ ^ 2) := by
  rw [pow_two, Complex.mul_re]
  simp [pow_two]

/--
`(iΘ)^2` の虚部評価。

`Im((iΘ)^2) = 0`。
-/
lemma pure_phase_sq_im (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ 2) = 0 := by
  rw [pow_two, Complex.mul_im]
  simp

/--
偶数冪 `(iΘ)^(2n)` の虚部は 0。
-/
lemma pure_phase_pow_even_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (2 * n)) = 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hdecomp : (Complex.I * Θ) ^ (2 * (n + 1)) =
          (Complex.I * Θ) ^ (2 * n) * (Complex.I * Θ) ^ 2 := by
        have htwo : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [htwo, pow_add]
      rw [hdecomp, Complex.mul_im, ih, pure_phase_sq_im]
      ring

/--
偶数冪 `(iΘ)^(2n)` の実部評価。

`Re((iΘ)^(2n)) = (-1)^n * Θ^(2n)`。
-/
lemma pure_phase_pow_even_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (2 * n)) = (-1 : ℝ) ^ n * Θ ^ (2 * n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hdecomp : (Complex.I * Θ) ^ (2 * (n + 1)) =
          (Complex.I * Θ) ^ (2 * n) * (Complex.I * Θ) ^ 2 := by
        have htwo : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [htwo, pow_add]
      rw [hdecomp, Complex.mul_re, ih, pure_phase_sq_re, pure_phase_pow_even_im, pure_phase_sq_im]
      have hpow1 : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) := by
        rw [pow_succ]
      have hpow2 : Θ ^ (2 * (n + 1)) = Θ ^ (2 * n) * Θ ^ 2 := by
        have htwo : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [htwo, pow_add]
      rw [hpow1, hpow2]
      ring

/--
奇数冪 `(iΘ)^(2n+1)` の実部は 0。
-/
lemma pure_phase_pow_odd_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (2 * n + 1)) = 0 := by
  calc
    Complex.re ((Complex.I * Θ) ^ (2 * n + 1))
        = Complex.re ((Complex.I * Θ) ^ (2 * n) * (Complex.I * Θ)) := by
            rw [pow_succ]
    _ = Complex.re ((Complex.I * Θ) ^ (2 * n)) * Complex.re (Complex.I * Θ)
          - Complex.im ((Complex.I * Θ) ^ (2 * n)) * Complex.im (Complex.I * Θ) := by
            rw [Complex.mul_re]
    _ = 0 := by
            simp [pure_phase_pow_even_im]

/--
奇数冪 `(iΘ)^(2n+1)` の虚部評価。

`Im((iΘ)^(2n+1)) = (-1)^n * Θ^(2n+1)`。
-/
lemma pure_phase_pow_odd_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (2 * n + 1)) = (-1 : ℝ) ^ n * Θ ^ (2 * n + 1) := by
  calc
    Complex.im ((Complex.I * Θ) ^ (2 * n + 1))
        = Complex.im ((Complex.I * Θ) ^ (2 * n) * (Complex.I * Θ)) := by
            rw [pow_succ]
    _ = Complex.re ((Complex.I * Θ) ^ (2 * n)) * Complex.im (Complex.I * Θ)
          + Complex.im ((Complex.I * Θ) ^ (2 * n)) * Complex.re (Complex.I * Θ) := by
            rw [Complex.mul_im]
    _ = (-1 : ℝ) ^ n * Θ ^ (2 * n) * Θ := by
            simp [pure_phase_pow_even_re, pure_phase_pow_even_im]
    _ = (-1 : ℝ) ^ n * Θ ^ (2 * n + 1) := by
            rw [pow_succ]
            ring

/--
実数上の `(-1)` の偶数冪。

`(-1)^(2n) = 1`。
-/
lemma neg_one_pow_even (n : ℕ) : (-1 : ℝ) ^ (2 * n) = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have htwo : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [htwo, pow_add]
      simp [ih]

/--
実数上の `(-1)` の奇数冪。

`(-1)^(2n+1) = -1`。
-/
lemma neg_one_pow_odd (n : ℕ) : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
  rw [pow_succ]
  simp

/--
`(iΘ)^(4n)` の実部。

`Re((iΘ)^(4n)) = Θ^(4n)`。
-/
lemma pure_phase_pow_mod4_zero_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n)) = Θ ^ (4 * n) := by
  have hfour : 4 * n = 2 * (2 * n) := by ring
  rw [hfour]
  rw [pure_phase_pow_even_re]
  simp

/--
`(iΘ)^(4n)` の虚部は 0。
-/
lemma pure_phase_pow_mod4_zero_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n)) = 0 := by
  have hfour : 4 * n = 2 * (2 * n) := by ring
  rw [hfour]
  simpa using pure_phase_pow_even_im (2 * n) Θ

/--
`(iΘ)^(4n+1)` の実部は 0。
-/
lemma pure_phase_pow_mod4_one_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 1)) = 0 := by
  have hfour : 4 * n + 1 = 2 * (2 * n) + 1 := by ring
  rw [hfour]
  simpa using pure_phase_pow_odd_re (2 * n) Θ

/--
`(iΘ)^(4n+1)` の虚部。

`Im((iΘ)^(4n+1)) = Θ^(4n+1)`。
-/
lemma pure_phase_pow_mod4_one_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n + 1)) = Θ ^ (4 * n + 1) := by
  have hfour : 4 * n + 1 = 2 * (2 * n) + 1 := by ring
  rw [hfour]
  rw [pure_phase_pow_odd_im]
  simp

/--
`(iΘ)^(4n+2)` の実部。

`Re((iΘ)^(4n+2)) = -Θ^(4n+2)`。
-/
lemma pure_phase_pow_mod4_two_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 2)) = -(Θ ^ (4 * n + 2)) := by
  have hfour : 4 * n + 2 = 2 * (2 * n + 1) := by ring
  rw [hfour]
  rw [pure_phase_pow_even_re]
  simp [neg_one_pow_odd]

/--
`(iΘ)^(4n+2)` の虚部は 0。
-/
lemma pure_phase_pow_mod4_two_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n + 2)) = 0 := by
  have hfour : 4 * n + 2 = 2 * (2 * n + 1) := by ring
  rw [hfour]
  simpa using pure_phase_pow_even_im (2 * n + 1) Θ

/--
`(iΘ)^(4n+3)` の実部は 0。
-/
lemma pure_phase_pow_mod4_three_re (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 3)) = 0 := by
  have hfour : 4 * n + 3 = 2 * (2 * n + 1) + 1 := by ring
  rw [hfour]
  simpa using pure_phase_pow_odd_re (2 * n + 1) Θ

/--
`(iΘ)^(4n+3)` の虚部。

`Im((iΘ)^(4n+3)) = -Θ^(4n+3)`。
-/
lemma pure_phase_pow_mod4_three_im (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n + 3)) = -(Θ ^ (4 * n + 3)) := by
  have hfour : 4 * n + 3 = 2 * (2 * n + 1) + 1 := by ring
  rw [hfour]
  rw [pure_phase_pow_odd_im]
  simp [neg_one_pow_odd]

/--
`d=2n` から `d+1=2n+1` への実部再帰（偶数相）。

`(iΘ)^(2n)` の実部評価を展開した形。
-/
lemma cfbrcRe_odd_from_even (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (2 * n + 1) X Θ =
      X * cfbrcRe (2 * n) X Θ - Θ * cfbrcIm (2 * n) X Θ +
        X * ((-1 : ℝ) ^ n * Θ ^ (2 * n)) := by
  simpa [pure_phase_pow_even_re] using cfbrcRe_succ' (d := 2 * n) X Θ

/--
`d=2n` から `d+1=2n+1` への虚部再帰（偶数相）。

`(iΘ)^(2n)` の虚部は 0 なので、右端項は消える。
-/
lemma cfbrcIm_odd_from_even (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (2 * n + 1) X Θ =
      X * cfbrcIm (2 * n) X Θ + Θ * cfbrcRe (2 * n) X Θ := by
  simpa [pure_phase_pow_even_im] using cfbrcIm_succ' (d := 2 * n) X Θ

/--
`d=2n+1` から `d+1=2n+2` への実部再帰（奇数相）。

`(iΘ)^(2n+1)` の実部は 0 なので、右端項は消える。
-/
lemma cfbrcRe_even_from_odd (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (2 * n + 2) X Θ =
      X * cfbrcRe (2 * n + 1) X Θ - Θ * cfbrcIm (2 * n + 1) X Θ := by
  simpa [pure_phase_pow_odd_re] using cfbrcRe_succ' (d := 2 * n + 1) X Θ

/--
`d=2n+1` から `d+1=2n+2` への虚部再帰（奇数相）。

`(iΘ)^(2n+1)` の虚部評価を展開した形。
-/
lemma cfbrcIm_even_from_odd (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (2 * n + 2) X Θ =
      X * cfbrcIm (2 * n + 1) X Θ + Θ * cfbrcRe (2 * n + 1) X Θ +
        X * ((-1 : ℝ) ^ n * Θ ^ (2 * n + 1)) := by
  simpa [pure_phase_pow_odd_im] using cfbrcIm_succ' (d := 2 * n + 1) X Θ

end

end DkMath.CFBRC.TrigBridge
