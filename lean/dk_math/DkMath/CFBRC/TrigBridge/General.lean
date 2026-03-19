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

end

end DkMath.CFBRC.TrigBridge
