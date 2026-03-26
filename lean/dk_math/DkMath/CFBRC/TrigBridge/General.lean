/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Basic
import Mathlib.Tactic

#print "file: DkMath.CFBRC.TrigBridge.General"

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
実数埋め込み冪 `((X:ℂ)^d)` の実部は `X^d`。
-/
lemma ofReal_pow_re (d : ℕ) (X : ℝ) : Complex.re ((X : ℂ) ^ d) = X ^ d := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [pow_succ, Complex.mul_re, ih]
      simp [pow_succ]

/--
実数埋め込み冪 `((X:ℂ)^d)` の虚部は 0。
-/
lemma ofReal_pow_im (d : ℕ) (X : ℝ) : Complex.im ((X : ℂ) ^ d) = 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [pow_succ, Complex.mul_im, ih]
      simp

/--
`Θ = 0` 断面（`d+1` 版）。

`cfbrcR (d+1) X 0 = X^(d+1)`。
-/
lemma cfbrcR_succ_theta_zero (d : ℕ) (X : ℝ) :
    cfbrcR (d + 1) X 0 = (X : ℂ) ^ (d + 1) := by
  simp [cfbrcR, cfbrc]

/--
`Θ = 0` 断面の実部（`d+1` 版）。

`cfbrcRe (d+1) X 0 = X^(d+1)`。
-/
lemma cfbrcRe_succ_theta_zero (d : ℕ) (X : ℝ) :
    cfbrcRe (d + 1) X 0 = X ^ (d + 1) := by
  rw [cfbrcRe, cfbrcR_succ_theta_zero]
  exact ofReal_pow_re (d + 1) X

/--
`Θ = 0` 断面の虚部（`d+1` 版）。

`cfbrcIm (d+1) X 0 = 0`。
-/
lemma cfbrcIm_succ_theta_zero (d : ℕ) (X : ℝ) :
    cfbrcIm (d + 1) X 0 = 0 := by
  rw [cfbrcIm, cfbrcR_succ_theta_zero]
  exact ofReal_pow_im (d + 1) X

/--
`X = 0` 断面。

`cfbrcR d 0 Θ = 0`（全ての `d`）。
-/
lemma cfbrcR_x_zero (d : ℕ) (Θ : ℝ) : cfbrcR d 0 Θ = 0 := by
  simp [cfbrcR, cfbrc]

/--
`X = 0` 断面の実部。

`cfbrcRe d 0 Θ = 0`。
-/
lemma cfbrcRe_x_zero (d : ℕ) (Θ : ℝ) : cfbrcRe d 0 Θ = 0 := by
  simp [cfbrcRe, cfbrcR_x_zero]

/--
`X = 0` 断面の虚部。

`cfbrcIm d 0 Θ = 0`。
-/
lemma cfbrcIm_x_zero (d : ℕ) (Θ : ℝ) : cfbrcIm d 0 Θ = 0 := by
  simp [cfbrcIm, cfbrcR_x_zero]

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
明示式を `d -> d+1` へ進める実部テンプレート。

`d` 次の実部・虚部の式と位相項の実部評価を与えると、
`d+1` 次の実部式を機械的に生成できる。
`d=8` 以降の展開を手書きせず進めるための雛形。
-/
lemma cfbrcRe_succ_template
    (d : ℕ) (X Θ ReD ImD phaseRe : ℝ)
    (hRe : cfbrcRe d X Θ = ReD)
    (hIm : cfbrcIm d X Θ = ImD)
    (hPhaseRe : Complex.re ((Complex.I * Θ) ^ d) = phaseRe) :
    cfbrcRe (d + 1) X Θ = X * ReD - Θ * ImD + X * phaseRe := by
  calc
    cfbrcRe (d + 1) X Θ =
        X * cfbrcRe d X Θ - Θ * cfbrcIm d X Θ + X * Complex.re ((Complex.I * Θ) ^ d) := by
          simpa using cfbrcRe_succ' d X Θ
    _ = X * ReD - Θ * ImD + X * phaseRe := by
          rw [hRe, hIm, hPhaseRe]

/--
明示式を `d -> d+1` へ進める虚部テンプレート。

`d` 次の実部・虚部の式と位相項の虚部評価を与えると、
`d+1` 次の虚部式を機械的に生成できる。
`cfbrcRe_succ_template` と対で使う。
-/
lemma cfbrcIm_succ_template
    (d : ℕ) (X Θ ReD ImD phaseIm : ℝ)
    (hRe : cfbrcRe d X Θ = ReD)
    (hIm : cfbrcIm d X Θ = ImD)
    (hPhaseIm : Complex.im ((Complex.I * Θ) ^ d) = phaseIm) :
    cfbrcIm (d + 1) X Θ = X * ImD + Θ * ReD + X * phaseIm := by
  calc
    cfbrcIm (d + 1) X Θ =
        X * cfbrcIm d X Θ + Θ * cfbrcRe d X Θ + X * Complex.im ((Complex.I * Θ) ^ d) := by
          simpa using cfbrcIm_succ' d X Θ
    _ = X * ImD + Θ * ReD + X * phaseIm := by
          rw [hRe, hIm, hPhaseIm]

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

/--
`d = 4n` から `d+1 = 4n+1` への実部再帰。

`(iΘ)^(4n)` の実部 `Θ^(4n)` を右端項へ代入した形。
-/
lemma cfbrcRe_mod4_one_from_zero (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 1) X Θ =
      X * cfbrcRe (4 * n) X Θ - Θ * cfbrcIm (4 * n) X Θ + X * Θ ^ (4 * n) := by
  simpa [pure_phase_pow_mod4_zero_re] using cfbrcRe_succ' (d := 4 * n) X Θ

/--
`d = 4n` から `d+1 = 4n+1` への虚部再帰。

`(iΘ)^(4n)` の虚部は `0` なので、右端項は消える。
-/
lemma cfbrcIm_mod4_one_from_zero (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 1) X Θ =
      X * cfbrcIm (4 * n) X Θ + Θ * cfbrcRe (4 * n) X Θ := by
  simpa [pure_phase_pow_mod4_zero_im] using cfbrcIm_succ' (d := 4 * n) X Θ

/--
`d = 4n+1` から `d+1 = 4n+2` への実部再帰。

`(iΘ)^(4n+1)` の実部は `0` なので、右端項は消える。
-/
lemma cfbrcRe_mod4_two_from_one (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 2) X Θ =
      X * cfbrcRe (4 * n + 1) X Θ - Θ * cfbrcIm (4 * n + 1) X Θ := by
  simpa [pure_phase_pow_mod4_one_re] using cfbrcRe_succ' (d := 4 * n + 1) X Θ

/--
`d = 4n+1` から `d+1 = 4n+2` への虚部再帰。

`(iΘ)^(4n+1)` の虚部 `Θ^(4n+1)` を右端項へ代入した形。
-/
lemma cfbrcIm_mod4_two_from_one (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 2) X Θ =
      X * cfbrcIm (4 * n + 1) X Θ + Θ * cfbrcRe (4 * n + 1) X Θ + X * Θ ^ (4 * n + 1) := by
  simpa [pure_phase_pow_mod4_one_im] using cfbrcIm_succ' (d := 4 * n + 1) X Θ

/--
`d = 4n+2` から `d+1 = 4n+3` への実部再帰。

`(iΘ)^(4n+2)` の実部 `-Θ^(4n+2)` を右端項へ代入した形。
-/
lemma cfbrcRe_mod4_three_from_two (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 3) X Θ =
      X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ - X * Θ ^ (4 * n + 2) := by
  calc
    cfbrcRe (4 * n + 3) X Θ = cfbrcRe ((4 * n + 2) + 1) X Θ := by ring_nf
    _ = X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ +
          X * Complex.re ((Complex.I * Θ) ^ (4 * n + 2)) := by
          simpa using cfbrcRe_succ' (d := 4 * n + 2) X Θ
    _ = X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ +
          X * (-(Θ ^ (4 * n + 2))) := by
          rw [pure_phase_pow_mod4_two_re]
    _ = X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ - X * Θ ^ (4 * n + 2) := by
          ring

/--
`d = 4n+2` から `d+1 = 4n+3` への虚部再帰。

`(iΘ)^(4n+2)` の虚部は `0` なので、右端項は消える。
-/
lemma cfbrcIm_mod4_three_from_two (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 3) X Θ =
      X * cfbrcIm (4 * n + 2) X Θ + Θ * cfbrcRe (4 * n + 2) X Θ := by
  simpa [pure_phase_pow_mod4_two_im] using cfbrcIm_succ' (d := 4 * n + 2) X Θ

/--
`d = 4n+3` から `d+1 = 4n+4` への実部再帰。

`(iΘ)^(4n+3)` の実部は `0` なので、右端項は消える。
-/
lemma cfbrcRe_mod4_four_from_three (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 4) X Θ =
      X * cfbrcRe (4 * n + 3) X Θ - Θ * cfbrcIm (4 * n + 3) X Θ := by
  simpa [pure_phase_pow_mod4_three_re] using cfbrcRe_succ' (d := 4 * n + 3) X Θ

/--
`d = 4n+3` から `d+1 = 4n+4` への虚部再帰。

`(iΘ)^(4n+3)` の虚部 `-Θ^(4n+3)` を右端項へ代入した形。
-/
lemma cfbrcIm_mod4_four_from_three (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 4) X Θ =
      X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ - X * Θ ^ (4 * n + 3) := by
  calc
    cfbrcIm (4 * n + 4) X Θ = cfbrcIm ((4 * n + 3) + 1) X Θ := by ring_nf
    _ = X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ +
          X * Complex.im ((Complex.I * Θ) ^ (4 * n + 3)) := by
          simpa using cfbrcIm_succ' (d := 4 * n + 3) X Θ
    _ = X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ +
          X * (-(Θ ^ (4 * n + 3))) := by
          rw [pure_phase_pow_mod4_three_im]
    _ = X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ - X * Θ ^ (4 * n + 3) := by
          ring

/--
低次数 `d=3` の実部明示式。

`cfbrcRe 3 X Θ = X^3 - 3XΘ^2`。
-/
lemma cfbrcRe_three (X Θ : ℝ) :
    cfbrcRe 3 X Θ = X ^ 3 - 3 * X * Θ ^ 2 := by
  simp [cfbrcRe, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=3` の虚部明示式。

`cfbrcIm 3 X Θ = 3X^2Θ`。
-/
lemma cfbrcIm_three (X Θ : ℝ) :
    cfbrcIm 3 X Θ = 3 * X ^ 2 * Θ := by
  simp [cfbrcIm, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=4` の実部明示式。

`cfbrcRe 4 X Θ = X^4 - 6X^2Θ^2`。
-/
lemma cfbrcRe_four (X Θ : ℝ) :
    cfbrcRe 4 X Θ = X ^ 4 - 6 * X ^ 2 * Θ ^ 2 := by
  simp [cfbrcRe, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=4` の虚部明示式。

`cfbrcIm 4 X Θ = 4X^3Θ - 4XΘ^3`。
-/
lemma cfbrcIm_four (X Θ : ℝ) :
    cfbrcIm 4 X Θ = 4 * X ^ 3 * Θ - 4 * X * Θ ^ 3 := by
  simp [cfbrcIm, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=5` の実部明示式。

`cfbrcRe 5 X Θ = X^5 - 10X^3Θ^2 + 5XΘ^4`。
-/
lemma cfbrcRe_five (X Θ : ℝ) :
    cfbrcRe 5 X Θ = X ^ 5 - 10 * X ^ 3 * Θ ^ 2 + 5 * X * Θ ^ 4 := by
  simp [cfbrcRe, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=5` の虚部明示式。

`cfbrcIm 5 X Θ = 5X^4Θ - 10X^2Θ^3`。
-/
lemma cfbrcIm_five (X Θ : ℝ) :
    cfbrcIm 5 X Θ = 5 * X ^ 4 * Θ - 10 * X ^ 2 * Θ ^ 3 := by
  simp [cfbrcIm, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=6` の実部明示式。

`cfbrcRe 6 X Θ = X^6 - 15X^4Θ^2 + 15X^2Θ^4`。
-/
lemma cfbrcRe_six (X Θ : ℝ) :
    cfbrcRe 6 X Θ = X ^ 6 - 15 * X ^ 4 * Θ ^ 2 + 15 * X ^ 2 * Θ ^ 4 := by
  simp [cfbrcRe, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=6` の虚部明示式。

`cfbrcIm 6 X Θ = 6X^5Θ - 20X^3Θ^3 + 6XΘ^5`。
-/
lemma cfbrcIm_six (X Θ : ℝ) :
    cfbrcIm 6 X Θ = 6 * X ^ 5 * Θ - 20 * X ^ 3 * Θ ^ 3 + 6 * X * Θ ^ 5 := by
  simp [cfbrcIm, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=7` の実部明示式。

`cfbrcRe 7 X Θ = X^7 - 21X^5Θ^2 + 35X^3Θ^4 - 7XΘ^6`。
-/
lemma cfbrcRe_seven (X Θ : ℝ) :
    cfbrcRe 7 X Θ = X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6 := by
  simp [cfbrcRe, cfbrcR, cfbrc, pow_succ]
  ring

/--
低次数 `d=7` の虚部明示式。

`cfbrcIm 7 X Θ = 7X^6Θ - 35X^4Θ^3 + 21X^2Θ^5`。
-/
lemma cfbrcIm_seven (X Θ : ℝ) :
    cfbrcIm 7 X Θ = 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5 := by
  simp [cfbrcIm, cfbrcR, cfbrc, pow_succ]
  ring

/--
再帰テンプレートで導く `d=8` 実部明示式。

`d=7` の明示式と `Re((iΘ)^7)=0` をテンプレートへ渡して生成する。
-/
lemma cfbrcRe_eight_from_template (X Θ : ℝ) :
    cfbrcRe 8 X Θ = X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 := by
  have hPhaseRe : Complex.re ((Complex.I * Θ) ^ 7) = 0 := by
    simpa using (pure_phase_pow_mod4_three_re (n := 1) Θ)
  have hStep :=
    cfbrcRe_succ_template
      (d := 7) (X := X) (Θ := Θ)
      (ReD := X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6)
      (ImD := 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5)
      (phaseRe := 0)
      (hRe := cfbrcRe_seven X Θ)
      (hIm := cfbrcIm_seven X Θ)
      (hPhaseRe := hPhaseRe)
  calc
    cfbrcRe 8 X Θ = X * (X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6) -
        Θ * (7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5) + X * 0 := by
          simpa using hStep
    _ = X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 := by
          ring

/--
再帰テンプレートで導く `d=8` 虚部明示式。

`d=7` の明示式と `Im((iΘ)^7)=-Θ^7` をテンプレートへ渡して生成する。
-/
lemma cfbrcIm_eight_from_template (X Θ : ℝ) :
    cfbrcIm 8 X Θ = 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 := by
  have hPhaseIm : Complex.im ((Complex.I * Θ) ^ 7) = -(Θ ^ 7) := by
    simpa using (pure_phase_pow_mod4_three_im (n := 1) Θ)
  have hStep :=
    cfbrcIm_succ_template
      (d := 7) (X := X) (Θ := Θ)
      (ReD := X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6)
      (ImD := 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5)
      (phaseIm := -(Θ ^ 7))
      (hRe := cfbrcRe_seven X Θ)
      (hIm := cfbrcIm_seven X Θ)
      (hPhaseIm := hPhaseIm)
  calc
    cfbrcIm 8 X Θ = X * (7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5) +
        Θ * (X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6) +
        X * (-(Θ ^ 7)) := by
          simpa using hStep
    _ = 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 := by
          ring

/--
再帰テンプレートで導く `d=9` 実部明示式。

`d=8` の明示式と `Re((iΘ)^8)=Θ^8` をテンプレートへ渡して生成する。
-/
lemma cfbrcRe_nine_from_template (X Θ : ℝ) :
    cfbrcRe 9 X Θ =
      X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 := by
  have hPhaseRe : Complex.re ((Complex.I * Θ) ^ 8) = Θ ^ 8 := by
    simpa using (pure_phase_pow_mod4_zero_re (n := 2) Θ)
  have hStep :=
    cfbrcRe_succ_template
      (d := 8) (X := X) (Θ := Θ)
      (ReD := X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6)
      (ImD := 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7)
      (phaseRe := Θ ^ 8)
      (hRe := cfbrcRe_eight_from_template X Θ)
      (hIm := cfbrcIm_eight_from_template X Θ)
      (hPhaseRe := hPhaseRe)
  calc
    cfbrcRe 9 X Θ =
        X * (X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6) -
        Θ * (8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7) +
        X * (Θ ^ 8) := by
          simpa using hStep
    _ = X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 := by
          ring

/--
再帰テンプレートで導く `d=9` 虚部明示式。

`d=8` の明示式と `Im((iΘ)^8)=0` をテンプレートへ渡して生成する。
-/
lemma cfbrcIm_nine_from_template (X Θ : ℝ) :
    cfbrcIm 9 X Θ =
      9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 := by
  have hPhaseIm : Complex.im ((Complex.I * Θ) ^ 8) = 0 := by
    simpa using (pure_phase_pow_mod4_zero_im (n := 2) Θ)
  have hStep :=
    cfbrcIm_succ_template
      (d := 8) (X := X) (Θ := Θ)
      (ReD := X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6)
      (ImD := 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7)
      (phaseIm := 0)
      (hRe := cfbrcRe_eight_from_template X Θ)
      (hIm := cfbrcIm_eight_from_template X Θ)
      (hPhaseIm := hPhaseIm)
  calc
    cfbrcIm 9 X Θ =
        X * (8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7) +
        Θ * (X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6) + X * 0 := by
          simpa using hStep
    _ = 9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 := by
          ring

/--
再帰テンプレートで導く `d=10` 実部明示式。

`d=9` の明示式と `Re((iΘ)^9)=0` をテンプレートへ渡して生成する。
-/
lemma cfbrcRe_ten_from_template (X Θ : ℝ) :
    cfbrcRe 10 X Θ =
      X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 := by
  have hPhaseRe : Complex.re ((Complex.I * Θ) ^ 9) = 0 := by
    simpa using (pure_phase_pow_mod4_one_re (n := 2) Θ)
  have hStep :=
    cfbrcRe_succ_template
      (d := 9) (X := X) (Θ := Θ)
      (ReD := X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8)
      (ImD := 9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7)
      (phaseRe := 0)
      (hRe := cfbrcRe_nine_from_template X Θ)
      (hIm := cfbrcIm_nine_from_template X Θ)
      (hPhaseRe := hPhaseRe)
  calc
    cfbrcRe 10 X Θ =
        X * (X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 +
          9 * X * Θ ^ 8) -
        Θ * (9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7) +
        X * 0 := by
          simpa using hStep
    _ = X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 := by
          ring

/--
再帰テンプレートで導く `d=10` 虚部明示式。

`d=9` の明示式と `Im((iΘ)^9)=Θ^9` をテンプレートへ渡して生成する。
-/
lemma cfbrcIm_ten_from_template (X Θ : ℝ) :
    cfbrcIm 10 X Θ =
      10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 := by
  have hPhaseIm : Complex.im ((Complex.I * Θ) ^ 9) = Θ ^ 9 := by
    simpa using (pure_phase_pow_mod4_one_im (n := 2) Θ)
  have hStep :=
    cfbrcIm_succ_template
      (d := 9) (X := X) (Θ := Θ)
      (ReD := X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8)
      (ImD := 9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7)
      (phaseIm := Θ ^ 9)
      (hRe := cfbrcRe_nine_from_template X Θ)
      (hIm := cfbrcIm_nine_from_template X Θ)
      (hPhaseIm := hPhaseIm)
  calc
    cfbrcIm 10 X Θ =
        X * (9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7) +
        Θ * (X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 +
          9 * X * Θ ^ 8) +
        X * (Θ ^ 9) := by
          simpa using hStep
    _ = 10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 := by
          ring

/--
再帰テンプレートで導く `d=11` 実部明示式。

`d=10` の明示式と `Re((iΘ)^10)=-Θ^10` をテンプレートへ渡して生成する。
-/
lemma cfbrcRe_eleven_from_template (X Θ : ℝ) :
    cfbrcRe 11 X Θ =
      X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
        165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 := by
  have hPhaseRe : Complex.re ((Complex.I * Θ) ^ 10) = -(Θ ^ 10) := by
    simpa using (pure_phase_pow_mod4_two_re (n := 2) Θ)
  have hStep :=
    cfbrcRe_succ_template
      (d := 10) (X := X) (Θ := Θ)
      (ReD := X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8)
      (ImD := 10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9)
      (phaseRe := -(Θ ^ 10))
      (hRe := cfbrcRe_ten_from_template X Θ)
      (hIm := cfbrcIm_ten_from_template X Θ)
      (hPhaseRe := hPhaseRe)
  calc
    cfbrcRe 11 X Θ =
        X * (X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
          210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8) -
        Θ * (10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
          120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9) +
        X * (-(Θ ^ 10)) := by
          simpa using hStep
    _ = X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
          165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 := by
          ring

/--
再帰テンプレートで導く `d=11` 虚部明示式。

`d=10` の明示式と `Im((iΘ)^10)=0` をテンプレートへ渡して生成する。
-/
lemma cfbrcIm_eleven_from_template (X Θ : ℝ) :
    cfbrcIm 11 X Θ =
      11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 := by
  have hPhaseIm : Complex.im ((Complex.I * Θ) ^ 10) = 0 := by
    simpa using (pure_phase_pow_mod4_two_im (n := 2) Θ)
  have hStep :=
    cfbrcIm_succ_template
      (d := 10) (X := X) (Θ := Θ)
      (ReD := X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8)
      (ImD := 10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9)
      (phaseIm := 0)
      (hRe := cfbrcRe_ten_from_template X Θ)
      (hIm := cfbrcIm_ten_from_template X Θ)
      (hPhaseIm := hPhaseIm)
  calc
    cfbrcIm 11 X Θ =
        X * (10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
          120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9) +
        Θ * (X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
          210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8) + X * 0 := by
          simpa using hStep
    _ = 11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
          330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 := by
          ring

/--
再帰テンプレートで導く `d=12` 実部明示式。

`d=11` の明示式と `Re((iΘ)^11)=0` をテンプレートへ渡して生成する。
-/
lemma cfbrcRe_twelve_from_template (X Θ : ℝ) :
    cfbrcRe 12 X Θ =
      X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
        495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 := by
  have hPhaseRe : Complex.re ((Complex.I * Θ) ^ 11) = 0 := by
    simpa using (pure_phase_pow_mod4_three_re (n := 2) Θ)
  have hStep :=
    cfbrcRe_succ_template
      (d := 11) (X := X) (Θ := Θ)
      (ReD := X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 -
        462 * X ^ 5 * Θ ^ 6 + 165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10)
      (ImD := 11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9)
      (phaseRe := 0)
      (hRe := cfbrcRe_eleven_from_template X Θ)
      (hIm := cfbrcIm_eleven_from_template X Θ)
      (hPhaseRe := hPhaseRe)
  calc
    cfbrcRe 12 X Θ =
        X * (X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 -
          462 * X ^ 5 * Θ ^ 6 + 165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10) -
        Θ * (11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
          330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9) +
        X * 0 := by
          simpa using hStep
    _ = X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
          495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 := by
          ring

/--
再帰テンプレートで導く `d=12` 虚部明示式。

`d=11` の明示式と `Im((iΘ)^11)=-Θ^11` をテンプレートへ渡して生成する。
-/
lemma cfbrcIm_twelve_from_template (X Θ : ℝ) :
    cfbrcIm 12 X Θ =
      12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
        792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 := by
  have hPhaseIm : Complex.im ((Complex.I * Θ) ^ 11) = -(Θ ^ 11) := by
    simpa using (pure_phase_pow_mod4_three_im (n := 2) Θ)
  have hStep :=
    cfbrcIm_succ_template
      (d := 11) (X := X) (Θ := Θ)
      (ReD := X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 -
        462 * X ^ 5 * Θ ^ 6 + 165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10)
      (ImD := 11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9)
      (phaseIm := -(Θ ^ 11))
      (hRe := cfbrcRe_eleven_from_template X Θ)
      (hIm := cfbrcIm_eleven_from_template X Θ)
      (hPhaseIm := hPhaseIm)
  calc
    cfbrcIm 12 X Θ =
        X * (11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
          330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9) +
        Θ * (X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 -
          462 * X ^ 5 * Θ ^ 6 + 165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10) +
        X * (-(Θ ^ 11)) := by
          simpa using hStep
    _ = 12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
          792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 := by
          ring

end

end DkMath.CFBRC.TrigBridge
