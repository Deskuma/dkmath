# CFBRC - Cosmic Formula Binomial Real Complex

CFBRC は、べき差
`(x+u)^d - u^d`
を「円分的な core（`cyclotomicPrimeCore`）」と
`GN`（`DkMath.CosmicFormulaBinom.GN`）で接続するための Lean 実装です。

直感的には、次の 3 層を橋渡しします。

1. 代数恒等式層: 差冪の因数分解と幾何和表現
2. 円分多項式層: `Φ_m` の評価・同次化評価（shifted eval）
3. 数論層: 除法判定、`padicValNat`、Zsigmondy primitive prime existence

参考:

- [CFBRC 理論メモ](/python/CFBRC/CFBRC.md)
- [CFBRC d=8 メモ](/python/CFBRC/CFBRC-d8.md)

## Core Formula

CFBRC の基本形（Nat/CommSemiring で扱う主対象）は

$$
(x+u)^d-u^d = x \cdot \mathrm{core}_d(x,u)
$$

で、Lean では `core_d(x,u)` に対応するものとして
`cyclotomicPrimeCore d x u` を用います。

複素数表記での原型:

$$
G_d(x,\theta)=(x+i\theta)^d-(i\theta)^d
$$

## Lean Modules

- `DkMath.CFBRC.Defs`
  - `cyclotomicPrimeCore` 定義
- `DkMath.CFBRC.Basic`
  - `cyclotomicPrimeCore` と `GN` の基本同一化
  - 差冪分解・除法同値の基本補題
- `DkMath.CFBRC.CyclotomicProduct`
  - `Φ_m` 評価器、divisors product bridge
  - general `u` で `cyclotomicDivisorsProductShifted = GN`
- `DkMath.CFBRC.Bridge`
  - valuation bridge (`padicValNat`)
  - Zsigmondy existence bridge
  - `BoundarySide` による左右統一 API
- `DkMath.CFBRC.TrigBridge.Main`
  - `d=2` の三角置換 bridge
  - `body2 = a^2 * cos^2 φ = Re(cfbrcR 2 (a cos φ) (a sin φ))`
- `DkMath.CFBRC.TrigBridge.General`
  - general `d` 向けの `Re/Im` 補助（基底値・再帰式・`(iΘ)^d` の偶奇補題）
  - `d=8` 以降のための再帰テンプレート（`cfbrcRe/Im_succ_template`）

## Quick Start

```lean
import DkMath.CFBRC
```

必要最小だけなら:

```lean
import DkMath.CFBRC.Basic
import DkMath.CFBRC.Bridge
```

Triangular Permutation の `d=2` bridge のみ使う場合:

```lean
import DkMath.CFBRC.TrigBridge.Main
```

## Usage Examples

### 1) Core と GN の同一化（Nat）

```lean
import DkMath.CFBRC.Basic

open DkMath.CFBRC
open DkMath.CosmicFormulaBinom

example {d x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore d x u = GN d x u :=
  cyclotomicPrimeCore_eq_GN_nat (p := d) (x := x) (u := u) hx
```

### 2) 素数除法の橋渡し

`q ∤ x` の下で
`q ∣ ((x+u)^p-u^p)` と `q ∣ cyclotomicPrimeCore p x u` は同値です。

```lean
import DkMath.CFBRC.Bridge

open DkMath.CFBRC

example {p x u q : ℕ} (hq : Nat.Prime q) (hqx : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u :=
  prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    (p := p) (x := x) (u := u) (q := q) hq hqx
```

### 3) valuation bridge（右境界）

```lean
import DkMath.CFBRC.Bridge

open DkMath.CFBRC
open DkMath.CosmicFormulaBinom

example {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hq : Nat.Prime q) (hqx : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ d - u ^ d) = padicValNat q (GN d x u) :=
  padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
    (d := d) (x := x) (u := u) (q := q) hd2 hx hu hq hqx
```

### 4) `BoundarySide` を使う左右統一 API

左右を統一した API では、`side` と境界除法条件を渡します。

```lean
import DkMath.CFBRC.Bridge

open DkMath.CFBRC

example {d x u q : ℕ}
    (side : BoundarySide)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hq : Nat.Prime q)
    (hqb : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryGN side d x u) :=
  padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
    side hd2 hx hu hcop hq hqb
```

### 5) Zsigmondy primitive prime existence（prime exponent）

```lean
import DkMath.CFBRC.Bridge

open DkMath.CFBRC

example {d x u : ℕ}
    (hd : Nat.Prime d) (hd3 : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x := by
  rcases exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary_of_coprime
      (d := d) (x := x) (u := u) hd hd3 hx hu hcop hnd with
    ⟨q, hqP, hqCore, hqnx, _hprim⟩
  exact ⟨q, hqP, hqCore, hqnx⟩
```

### 6) Triangular Permutation bridge（`d=2`）

```lean
import DkMath.CFBRC.TrigBridge.Main

open DkMath.CFBRC.TrigBridge

example (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  body2_eq_re_cfbrc2 a φ

example (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) :=
  factor_eq_re_cfbrc2 a φ

example (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 :=
  cfbrc_two_re_via_general X Θ

example (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 :=
  cfbrc_two_re X Θ

example (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ :=
  cfbrc_two_im_polar_via_general a φ
```

### 7) General `d` 用の `Re/Im` 補助

```lean
import DkMath.CFBRC.TrigBridge.General

open DkMath.CFBRC.TrigBridge

example (d : ℕ) (X Θ : ℝ) :
    cfbrcRe (d + 1) X Θ =
      X * cfbrcRe d X Θ - Θ * cfbrcIm d X Θ + X * Complex.re ((Complex.I * Θ) ^ d) :=
  cfbrcRe_succ' d X Θ

example (d : ℕ) (X Θ ReD ImD phaseRe : ℝ)
    (hRe : cfbrcRe d X Θ = ReD)
    (hIm : cfbrcIm d X Θ = ImD)
    (hPhaseRe : Complex.re ((Complex.I * Θ) ^ d) = phaseRe) :
    cfbrcRe (d + 1) X Θ = X * ReD - Θ * ImD + X * phaseRe :=
  cfbrcRe_succ_template d X Θ ReD ImD phaseRe hRe hIm hPhaseRe

example (n : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ (2 * n + 1)) = (-1 : ℝ) ^ n * Θ ^ (2 * n + 1) :=
  pure_phase_pow_odd_im n Θ

example (n : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ (4 * n + 2)) = -(Θ ^ (4 * n + 2)) :=
  pure_phase_pow_mod4_two_re n Θ

example (n : ℕ) (X Θ : ℝ) :
    cfbrcIm (4 * n + 4) X Θ =
      X * cfbrcIm (4 * n + 3) X Θ + Θ * cfbrcRe (4 * n + 3) X Θ - X * Θ ^ (4 * n + 3) :=
  cfbrcIm_mod4_four_from_three n X Θ

example (d : ℕ) (X : ℝ) :
    cfbrcRe (d + 1) X 0 = X ^ (d + 1) :=
  cfbrcRe_succ_theta_zero d X

example (X Θ : ℝ) :
    cfbrcRe 5 X Θ = X ^ 5 - 10 * X ^ 3 * Θ ^ 2 + 5 * X * Θ ^ 4 :=
  cfbrcRe_five X Θ

example (X Θ : ℝ) :
    cfbrcIm 5 X Θ = 5 * X ^ 4 * Θ - 10 * X ^ 2 * Θ ^ 3 :=
  cfbrcIm_five X Θ

example (X Θ : ℝ) :
    cfbrcRe 7 X Θ = X ^ 7 - 21 * X ^ 5 * Θ ^ 2 + 35 * X ^ 3 * Θ ^ 4 - 7 * X * Θ ^ 6 :=
  cfbrcRe_seven X Θ

example (X Θ : ℝ) :
    cfbrcIm 7 X Θ = 7 * X ^ 6 * Θ - 35 * X ^ 4 * Θ ^ 3 + 21 * X ^ 2 * Θ ^ 5 :=
  cfbrcIm_seven X Θ

example (X Θ : ℝ) :
    cfbrcRe 8 X Θ = X ^ 8 - 28 * X ^ 6 * Θ ^ 2 + 70 * X ^ 4 * Θ ^ 4 - 28 * X ^ 2 * Θ ^ 6 :=
  cfbrcRe_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 8 X Θ = 8 * X ^ 7 * Θ - 56 * X ^ 5 * Θ ^ 3 + 56 * X ^ 3 * Θ ^ 5 - 8 * X * Θ ^ 7 :=
  cfbrcIm_eight_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 9 X Θ =
      X ^ 9 - 36 * X ^ 7 * Θ ^ 2 + 126 * X ^ 5 * Θ ^ 4 - 84 * X ^ 3 * Θ ^ 6 + 9 * X * Θ ^ 8 :=
  cfbrcRe_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 9 X Θ =
      9 * X ^ 8 * Θ - 84 * X ^ 6 * Θ ^ 3 + 126 * X ^ 4 * Θ ^ 5 - 36 * X ^ 2 * Θ ^ 7 :=
  cfbrcIm_nine_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 10 X Θ =
      X ^ 10 - 45 * X ^ 8 * Θ ^ 2 + 210 * X ^ 6 * Θ ^ 4 - 210 * X ^ 4 * Θ ^ 6 + 45 * X ^ 2 * Θ ^ 8 :=
  cfbrcRe_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 10 X Θ =
      10 * X ^ 9 * Θ - 120 * X ^ 7 * Θ ^ 3 + 252 * X ^ 5 * Θ ^ 5 - 120 * X ^ 3 * Θ ^ 7 + 10 * X * Θ ^ 9 :=
  cfbrcIm_ten_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 11 X Θ =
      X ^ 11 - 55 * X ^ 9 * Θ ^ 2 + 330 * X ^ 7 * Θ ^ 4 - 462 * X ^ 5 * Θ ^ 6 +
        165 * X ^ 3 * Θ ^ 8 - 11 * X * Θ ^ 10 :=
  cfbrcRe_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 11 X Θ =
      11 * X ^ 10 * Θ - 165 * X ^ 8 * Θ ^ 3 + 462 * X ^ 6 * Θ ^ 5 -
        330 * X ^ 4 * Θ ^ 7 + 55 * X ^ 2 * Θ ^ 9 :=
  cfbrcIm_eleven_from_template X Θ

example (X Θ : ℝ) :
    cfbrcRe 12 X Θ =
      X ^ 12 - 66 * X ^ 10 * Θ ^ 2 + 495 * X ^ 8 * Θ ^ 4 - 924 * X ^ 6 * Θ ^ 6 +
        495 * X ^ 4 * Θ ^ 8 - 66 * X ^ 2 * Θ ^ 10 :=
  cfbrcRe_twelve_from_template X Θ

example (X Θ : ℝ) :
    cfbrcIm 12 X Θ =
      12 * X ^ 11 * Θ - 220 * X ^ 9 * Θ ^ 3 + 792 * X ^ 7 * Θ ^ 5 -
        792 * X ^ 5 * Θ ^ 7 + 220 * X ^ 3 * Θ ^ 9 - 12 * X * Θ ^ 11 :=
  cfbrcIm_twelve_from_template X Θ
```

## Related Docs

- [Implements Design](./docs/CFBRC_Implements_Design.md)
- [Implements History](./docs/CFBRC_Implements_History.md)
- [Discussion](./docs/CFBRC_Discussion.md)

## Notes

- `Bridge` は既存の数論定理を改変せず、CFBRC 記法へ再輸出する薄い層です。
- valuation API は Nat の `padicValNat` 文脈に合わせて設計されています。
- general `u` の product 同一化は `CyclotomicProduct` に集約されています。
