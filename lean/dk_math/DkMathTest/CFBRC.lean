import DkMath.CFBRC

/-! # DkMathTest.CFBRC

`DkMath.CFBRC` 公開 API の回帰検証ファイル。

- `TrigBridge` (`d=2`) の橋定理
- core/GN の除法橋
- `BoundarySide` 高位 API（valuation / existence）

を `example` で固定し、将来の型崩れ・命名変更を検知する。
-/

#print "file: DkMathTest.CFBRC"

namespace DkMathTest.CFBRC

open DkMath.CFBRC
open DkMath.CFBRC.TrigBridge
open DkMath.CosmicFormulaBinom

-- d=2 三角置換 bridge
example (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  body2_eq_re_cfbrc2 a φ

example (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  factor_eq_re_cfbrc2 a φ

example (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 := by
  simpa using cfbrc_two_re_via_general X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 := by
  simpa using cfbrc_two_re X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcR 2 X Θ) = 2 * X * Θ := by
  simpa using cfbrc_two_im_via_general X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcR 2 X Θ) = 2 * X * Θ := by
  simpa using cfbrc_two_im X Θ

example (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ := by
  simpa using cfbrc_two_im_polar_via_general a φ

example (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ := by
  simpa using cfbrc_two_im_polar a φ

-- core と GN の橋
example {p x u q : ℕ} (hq : Nat.Prime q) (hqx : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u :=
  prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    (p := p) (x := x) (u := u) (q := q) hq hqx

example {d x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore d x u = GN d x u :=
  cyclotomicPrimeCore_eq_GN_nat (p := d) (x := x) (u := u) hx

-- general d の Re/Im 補助
example (X Θ : ℝ) :
    cfbrcRe 1 X Θ = X := by
  exact cfbrcRe_one X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcRe (d + 1) X Θ =
      X * cfbrcRe d X Θ - Θ * cfbrcIm d X Θ + X * Complex.re ((Complex.I * Θ) ^ d) := by
  simpa using cfbrcRe_succ' d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcIm (d + 1) X Θ =
      X * cfbrcIm d X Θ + Θ * cfbrcRe d X Θ + X * Complex.im ((Complex.I * Θ) ^ d) := by
  simpa using cfbrcIm_succ' d X Θ

example (d : ℕ) (X Θ ReD ImD phaseRe : ℝ)
    (hRe : cfbrcRe d X Θ = ReD)
    (hIm : cfbrcIm d X Θ = ImD)
    (hPhaseRe : Complex.re ((Complex.I * Θ) ^ d) = phaseRe) :
    cfbrcRe (d + 1) X Θ = X * ReD - Θ * ImD + X * phaseRe := by
  simpa using cfbrcRe_succ_template d X Θ ReD ImD phaseRe hRe hIm hPhaseRe

example (d : ℕ) (X Θ ReD ImD phaseIm : ℝ)
    (hRe : cfbrcRe d X Θ = ReD)
    (hIm : cfbrcIm d X Θ = ImD)
    (hPhaseIm : Complex.im ((Complex.I * Θ) ^ d) = phaseIm) :
    cfbrcIm (d + 1) X Θ = X * ImD + Θ * ReD + X * phaseIm := by
  simpa using cfbrcIm_succ_template d X Θ ReD ImD phaseIm hRe hIm hPhaseIm

example (d : ℕ) (X Θ : ℝ) :
    cfbrcR d X Θ = cfbrcClosed d X Θ := by
  simpa using cfbrcR_eq_cfbrcClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcRe d X Θ = cfbrcReClosedRaw d X Θ := by
  simpa using cfbrcRe_eq_cfbrcReClosedRaw d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcIm d X Θ = cfbrcImClosedRaw d X Θ := by
  simpa using cfbrcIm_eq_cfbrcImClosedRaw d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcReClosedRaw d X Θ = cfbrcReClosed d X Θ := by
  simpa using cfbrcReClosedRaw_eq_cfbrcReClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcImClosedRaw d X Θ = cfbrcImClosed d X Θ := by
  simpa using cfbrcImClosedRaw_eq_cfbrcImClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcRe d X Θ = cfbrcReClosed d X Θ := by
  simpa using cfbrcRe_eq_cfbrcReClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    cfbrcIm d X Θ = cfbrcImClosed d X Θ := by
  simpa using cfbrcIm_eq_cfbrcImClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    Complex.re (cfbrcClosed d X Θ) = cfbrcReClosed d X Θ := by
  simpa using cfbrcClosed_re_eq_cfbrcReClosed d X Θ

example (d : ℕ) (X Θ : ℝ) :
    Complex.im (cfbrcClosed d X Θ) = cfbrcImClosed d X Θ := by
  simpa using cfbrcClosed_im_eq_cfbrcImClosed d X Θ

private lemma cfbrcClosed_re_eq_cfbrcRe_via_closed (d : ℕ) (X Θ : ℝ) :
    Complex.re (cfbrcClosed d X Θ) = cfbrcRe d X Θ := by
  calc
    Complex.re (cfbrcClosed d X Θ) = cfbrcReClosed d X Θ := by
      simpa using cfbrcClosed_re_eq_cfbrcReClosed d X Θ
    _ = cfbrcRe d X Θ := by
      simpa using (cfbrcRe_eq_cfbrcReClosed d X Θ).symm

private lemma cfbrcClosed_im_eq_cfbrcIm_via_closed (d : ℕ) (X Θ : ℝ) :
    Complex.im (cfbrcClosed d X Θ) = cfbrcIm d X Θ := by
  calc
    Complex.im (cfbrcClosed d X Θ) = cfbrcImClosed d X Θ := by
      simpa using cfbrcClosed_im_eq_cfbrcImClosed d X Θ
    _ = cfbrcIm d X Θ := by
      simpa using (cfbrcIm_eq_cfbrcImClosed d X Θ).symm

example (d : ℕ) (X : ℝ) :
    cfbrcRe (d + 1) X 0 = X ^ (d + 1) := by
  simpa using cfbrcRe_succ_theta_zero d X

example (d : ℕ) (Θ : ℝ) :
    cfbrcRe d 0 Θ = 0 := by
  simpa using cfbrcRe_x_zero d Θ

example (d : ℕ) (Θ : ℝ) :
    cfbrcIm d 0 Θ = 0 := by
  simpa using cfbrcIm_x_zero d Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (2 * n)) = (-1 : ℝ) ^ n * Θ ^ (2 * n) := by
  simpa using pure_phase_pow_even_re n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (2 * n + 1)) = (-1 : ℝ) ^ n * Θ ^ (2 * n + 1) := by
  simpa using pure_phase_pow_odd_im n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 2)) = -(Θ ^ (4 * n + 2)) := by
  simpa using pure_phase_pow_mod4_two_re n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (4 * n + 3)) = -(Θ ^ (4 * n + 3)) := by
  simpa using pure_phase_pow_mod4_three_im n Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (2 * n + 2) X Θ =
      X * cfbrcIm (2 * n + 1) X Θ + Θ * cfbrcRe (2 * n + 1) X Θ +
        X * ((-1 : ℝ) ^ n * Θ ^ (2 * n + 1)) := by
  simpa using cfbrcIm_even_from_odd n X Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcRe (4 * n + 3) X Θ =
      X * cfbrcRe (4 * n + 2) X Θ - Θ * cfbrcIm (4 * n + 2) X Θ - X * Θ ^ (4 * n + 2) := by
  simpa using cfbrcRe_mod4_three_from_two n X Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 4) X Θ =
      X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ - X * Θ ^ (4 * n + 3) := by
  simpa using cfbrcIm_mod4_four_from_three n X Θ

example (X Θ : ℝ) :
    cfbrcRe 3 X Θ = X ^ 3 - 3 * X * Θ ^ 2 := by
  simpa using cfbrcRe_three X Θ

example (X Θ : ℝ) :
    cfbrcIm 3 X Θ = 3 * X ^ 2 * Θ := by
  simpa using cfbrcIm_three X Θ

example (X Θ : ℝ) :
    cfbrcRe 4 X Θ = X ^ 4 - 6 * X ^ 2 * Θ ^ 2 := by
  simpa using cfbrcRe_four X Θ

example (X Θ : ℝ) :
    cfbrcIm 4 X Θ = 4 * X ^ 3 * Θ - 4 * X * Θ ^ 3 := by
  simpa using cfbrcIm_four X Θ

example (X Θ : ℝ) :
    cfbrcRe 5 X Θ = X ^ 5 - 10 * X ^ 3 * Θ ^ 2 + 5 * X * Θ ^ 4 := by
  simpa using cfbrcRe_five X Θ

example (X Θ : ℝ) :
    cfbrcIm 5 X Θ = 5 * X ^ 4 * Θ - 10 * X ^ 2 * Θ ^ 3 := by
  simpa using cfbrcIm_five X Θ

example (X Θ : ℝ) :
    cfbrcRe 6 X Θ = X ^ 6 - 15 * X ^ 4 * Θ ^ 2 + 15 * X ^ 2 * Θ ^ 4 := by
  simpa using cfbrcRe_six X Θ

example (X Θ : ℝ) :
    cfbrcIm 6 X Θ = 6 * X ^ 5 * Θ - 20 * X ^ 3 * Θ ^ 3 + 6 * X * Θ ^ 5 := by
  simpa using cfbrcIm_six X Θ

example (X Θ : ℝ) :
    cfbrcRe 7 X Θ = X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6 := by
  simpa using cfbrcRe_seven X Θ

example (X Θ : ℝ) :
    cfbrcIm 7 X Θ = 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5 := by
  simpa using cfbrcIm_seven X Θ

example (X Θ : ℝ) :
    cfbrcRe 8 X Θ = X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 := by
  simpa using cfbrcRe_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 8 X Θ = 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 := by
  simpa using cfbrcIm_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 9 X Θ =
      X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 := by
  simpa using cfbrcRe_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 9 X Θ =
      9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 := by
  simpa using cfbrcIm_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 10 X Θ =
      X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 := by
  simpa using cfbrcRe_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 10 X Θ =
      10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 := by
  simpa using cfbrcIm_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 11 X Θ =
      X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
        165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 := by
  simpa using cfbrcRe_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 11 X Θ =
      11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 := by
  simpa using cfbrcIm_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 12 X Θ =
      X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
        495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 := by
  simpa using cfbrcRe_twelve_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 12 X Θ =
      12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
        792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 := by
  simpa using cfbrcIm_twelve_from_template X Θ

-- d=3..12 回帰（`cfbrcClosed` 実部/虚部 -> `cfbrcRe/ImClosed` 経由）
example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 3 X Θ) = X ^ 3 - 3 * X * Θ ^ 2 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_three X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 3 X Θ) = 3 * X ^ 2 * Θ := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_three X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 4 X Θ) = X ^ 4 - 6 * X ^ 2 * Θ ^ 2 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_four X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 4 X Θ) = 4 * X ^ 3 * Θ - 4 * X * Θ ^ 3 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_four X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 5 X Θ) = X ^ 5 - 10 * X ^ 3 * Θ ^ 2 + 5 * X * Θ ^ 4 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_five X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 5 X Θ) = 5 * X ^ 4 * Θ - 10 * X ^ 2 * Θ ^ 3 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_five X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 6 X Θ) = X ^ 6 - 15 * X ^ 4 * Θ ^ 2 + 15 * X ^ 2 * Θ ^ 4 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_six X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 6 X Θ) = 6 * X ^ 5 * Θ - 20 * X ^ 3 * Θ ^ 3 + 6 * X * Θ ^ 5 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_six X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 7 X Θ) =
      X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_seven X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 7 X Θ) = 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_seven X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 8 X Θ) =
      X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_eight_from_template X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 8 X Θ) =
      8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_eight_from_template X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 9 X Θ) =
      X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_nine_from_template X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 9 X Θ) =
      9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_nine_from_template X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 10 X Θ) =
      X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_ten_from_template X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 10 X Θ) =
      10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_ten_from_template X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 11 X Θ) =
      X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
        165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_eleven_from_template X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 11 X Θ) =
      11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_eleven_from_template X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcClosed 12 X Θ) =
      X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
        495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 := by
  simpa [cfbrcClosed_re_eq_cfbrcRe_via_closed] using cfbrcRe_twelve_from_template X Θ

example (X Θ : ℝ) :
    Complex.im (cfbrcClosed 12 X Θ) =
      12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
        792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 := by
  simpa [cfbrcClosed_im_eq_cfbrcIm_via_closed] using cfbrcIm_twelve_from_template X Θ

-- d=3..12 回帰（`cfbrcReClosed` / `cfbrcImClosed` 主語）
private lemma cfbrcReClosed_eq_cfbrcRe_via_api (d : ℕ) (X Θ : ℝ) :
    cfbrcReClosed d X Θ = cfbrcRe d X Θ := by
  simpa using (cfbrcRe_eq_cfbrcReClosed d X Θ).symm

private lemma cfbrcImClosed_eq_cfbrcIm_via_api (d : ℕ) (X Θ : ℝ) :
    cfbrcImClosed d X Θ = cfbrcIm d X Θ := by
  simpa using (cfbrcIm_eq_cfbrcImClosed d X Θ).symm

example (X Θ : ℝ) :
    cfbrcReClosed 3 X Θ = X ^ 3 - 3 * X * Θ ^ 2 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_three X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 3 X Θ = 3 * X ^ 2 * Θ := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_three X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 4 X Θ = X ^ 4 - 6 * X ^ 2 * Θ ^ 2 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_four X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 4 X Θ = 4 * X ^ 3 * Θ - 4 * X * Θ ^ 3 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_four X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 5 X Θ = X ^ 5 - 10 * X ^ 3 * Θ ^ 2 + 5 * X * Θ ^ 4 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_five X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 5 X Θ = 5 * X ^ 4 * Θ - 10 * X ^ 2 * Θ ^ 3 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_five X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 6 X Θ = X ^ 6 - 15 * X ^ 4 * Θ ^ 2 + 15 * X ^ 2 * Θ ^ 4 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_six X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 6 X Θ = 6 * X ^ 5 * Θ - 20 * X ^ 3 * Θ ^ 3 + 6 * X * Θ ^ 5 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_six X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 7 X Θ =
      X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_seven X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 7 X Θ = 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_seven X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 8 X Θ =
      X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 8 X Θ =
      8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 9 X Θ =
      X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 9 X Θ =
      9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 10 X Θ =
      X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 -
        210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 10 X Θ =
      10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 -
        120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 11 X Θ =
      X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
        165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 11 X Θ =
      11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcReClosed 12 X Θ =
      X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
        495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 := by
  simpa [cfbrcReClosed_eq_cfbrcRe_via_api] using cfbrcRe_twelve_from_template X Θ

example (X Θ : ℝ) :
    cfbrcImClosed 12 X Θ =
      12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
        792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 := by
  simpa [cfbrcImClosed_eq_cfbrcIm_via_api] using cfbrcIm_twelve_from_template X Θ

-- BoundarySide 高位 API（valuation）
example (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryGN side d x u) :=
  padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
    side hd2 hx hu hcop hqP hq_dvd_boundary

example (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryCyclotomicPrimeCore side d x u) :=
  padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary
    side hd2 hx hu hcop hqP hq_dvd_boundary

-- BoundarySide 高位 API（existence）
example (side : BoundarySide) {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ boundaryCyclotomicPrimeCore side d x u ∧
      (match side with
        | .right => ¬ q ∣ x
        | .left => ¬ q ∣ u) ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ boundaryDiffPow side k x u) :=
  exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime
    side hd_prime hd_ge hx hu hcop hpnd

example (side : BoundarySide) {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : match side with
      | .right => ¬ d ∣ x
      | .left => ¬ d ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ boundaryDiffPow side d x u ∧
      (match side with
        | .right => ¬ q ∣ x
        | .left => ¬ q ∣ u) ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ boundaryDiffPow side k x u) :=
  exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime
    side hd_prime hd_ge hx hu hcop hpnd

-- 依存公理の確認（回帰用）
#print axioms factor_eq_re_cfbrc2
#print axioms cfbrc_two_re_via_general
#print axioms cfbrc_two_re
#print axioms cfbrc_two_im_polar_via_general
#print axioms cfbrc_two_im_polar
#print axioms prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
#print axioms cfbrcRe_succ'
#print axioms cfbrcRe_succ_template
#print axioms cfbrcR_eq_cfbrcClosed
#print axioms cfbrcRe_eq_cfbrcReClosedRaw
#print axioms cfbrcRe_eq_cfbrcReClosed
#print axioms cfbrcIm_eq_cfbrcImClosed
#print axioms cfbrcClosed_re_eq_cfbrcReClosed
#print axioms cfbrcClosed_im_eq_cfbrcImClosed
#print axioms cfbrcRe_succ_theta_zero
#print axioms pure_phase_pow_odd_im
#print axioms pure_phase_pow_mod4_three_im
#print axioms cfbrcIm_mod4_four_from_three
#print axioms cfbrcRe_five
#print axioms cfbrcIm_seven
#print axioms cfbrcRe_eight_from_template
#print axioms cfbrcIm_ten_from_template
#print axioms cfbrcIm_twelve_from_template
#print axioms padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
#print axioms exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime
#print axioms exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime

end DkMathTest.CFBRC
