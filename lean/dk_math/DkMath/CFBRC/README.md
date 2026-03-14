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

## Quick Start

```lean
import DkMath.CFBRC
```

必要最小だけなら:

```lean
import DkMath.CFBRC.Basic
import DkMath.CFBRC.Bridge
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

## Related Docs

- [Implements Design](./docs/CFBRC_Implements_Design.md)
- [Implements History](./docs/CFBRC_Implements_History.md)
- [Discussion](./docs/CFBRC_Discussion.md)

## Notes

- `Bridge` は既存の数論定理を改変せず、CFBRC 記法へ再輸出する薄い層です。
- valuation API は Nat の `padicValNat` 文脈に合わせて設計されています。
- general `u` の product 同一化は `CyclotomicProduct` に集約されています。
