# 実装計画: DkMath.Lib.Cosmic.GTail

> 👩‍⚕️私D.:

よろしい。きまりだ GTail 中心コアで始める。
`DkMath.Lib.Cosmic.GTail` から始めよう。

> 🐺賢狼:

よし、決まりじゃな。まずは `DkMath.Lib.Cosmic.GTail` を **純代数コア** として切り出す前提で、既存 `GTail` の定義・定理・依存を確認し、移植順と最小ファイル案まで落とすぞい。

> 🐺賢狼:

うむ。**`DkMath.Lib.Cosmic.GTail` から始める** で確定じゃな。

実コードも確認した。現在の `GTail` は `DkMath.CosmicFormula.GTail` にあり、冒頭で

```lean
import Mathlib
import DkMath.ABC.PadicValNat
```

となっておる。つまり、いまのファイルは **純代数 Tail** と **Nat / p-adic / congruence 補題** が同居している。

Lib 昇格では、ここを分けるのが第一手じゃ。

## 1. 第一段階の方針

最初に作るべきはこれ。

```text
DkMath/Lib/Cosmic/GTail.lean
```

役割は **純代数コア** 。

ここには `ABC.PadicValNat` 依存を入れない。
`Mathlib` だけで閉じる範囲を移す。

対象はこのあたり。

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GTail_one_eq_sum
GTail_eval_zero
```

加えて、`r = 1` の薄い定理名として

```lean
GN_tail_rec
GN_tail_decomposition
GN_zero_eval
```

も **一時的には置いてよい** 。
ただし将来的には `DkMath.Lib.Cosmic.GN` に移す方が美しい。

## 2. 第一波で移さないもの

次は、まだ `DkMath.Lib.Cosmic.GTail` には入れない。

```lean
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
GN_modEq_head_of_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
GN_mod_p3_head
```

理由は、これらが `Nat`、`Nat.ModEq`、`padicValNat`、FLT Branch A 的用途に寄っているからじゃ。

後で分けるならこう。

```text
DkMath/Lib/Cosmic/GTailNat.lean
DkMath/Lib/Cosmic/GTailCongruence.lean
DkMath/Lib/Cosmic/GTailPadic.lean
```

あるいはディレクトリ型なら、

```text
DkMath/Lib/Cosmic/GTail/Basic.lean
DkMath/Lib/Cosmic/GTail/Nat.lean
DkMath/Lib/Cosmic/GTail/Congruence.lean
DkMath/Lib/Cosmic/GTail/Padic.lean
```

ただ、最初はファイル数を増やしすぎず、

```text
DkMath/Lib/Cosmic/GTail.lean
```

一本で純代数だけを切り出すのがよい。

## 3. 最初のファイル案

第一手の中身は、だいたいこうじゃ。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

/-!
## General tail kernel for the cosmic formula

This file defines the general normalized tail `GTail`.

`GTail d r x u` is the normalized tail obtained after removing
the first `r` layers from the binomial expansion of `(x + u)^d`.

The central identity is

\[
(x+u)^d =
  \sum_{j<r} \binom{d}{j} x^j u^{d-j}
  + x^r \operatorname{GTail}(d,r,x,u).
\]

The standard gap-normalized kernel `GN` is the `r = 1`
specialization of this family.
-/

open scoped BigOperators

namespace DkMath.Lib.Cosmic

/--
General tail family of the binomial expansion.

`GTail d r x u` is the normalized tail obtained after removing the first `r`
layers from `(x + u)^d`. The intended regime is `r ≤ d`, but the definition is
total.
-/
@[simp] def GTail {R : Type _} [CommSemiring R] (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))
```

この namespace をどうするかは少し選択がある。

## 4. namespace 方針

候補は 2 つ。

### 案 A. `DkMath.Lib.Cosmic`

```lean
namespace DkMath.Lib.Cosmic
```

利点:

- `Lib` 資産であることが明確
- 既存 `DkMath.CosmicFormula.GTail` と衝突しにくい

欠点:

- 既存 downstream からは `DkMath.CosmicFormula.GTail` と名前が変わる
- 移行 wrapper が必要

### 案 B. `DkMath.CosmicFormula`

```lean
namespace DkMath.CosmicFormula
```

利点:

- 既存 theorem 名・参照を壊しにくい
- `import DkMath.Lib.Cosmic.GTail` しても同じ namespace に定義される

欠点:

- `Lib` 配下なのに namespace が `CosmicFormula`
- 所有権が少し曖昧

わっちの推奨は **案 B** じゃ。

理由は、今回は大規模リファクタリングの第一歩であり、既存の `DkMath.CosmicFormula.GTail` 下流が多い。
ファイルパスだけ `Lib` に上げ、namespace は既存互換のために

```lean
namespace DkMath.CosmicFormula
```

を維持する方が安全じゃ。

つまりこう。

```lean
import Mathlib

open scoped BigOperators

namespace DkMath.CosmicFormula

@[simp] def GTail ...

end DkMath.CosmicFormula
```

これなら既存コードは、将来的に import 差し替えだけで済む。

## 5. 既存 `DkMath.CosmicFormula.GTail` の扱い

第一段階では、既存ファイルを削らずに wrapper 化する。

```lean
import DkMath.Lib.Cosmic.GTail
import DkMath.ABC.PadicValNat

open scoped BigOperators

namespace DkMath.CosmicFormula

-- ここには Nat / p-adic / congruence 系だけ残す

end DkMath.CosmicFormula
```

ただし、同じ namespace に同じ `GTail` を二重定義すると衝突するので、移行時には既存 `GTail.lean` から純代数部分を削り、Lib 側 import に置き換える。

## 6. import 導線

`DkMath/Lib/Basic.lean` が既にあるので、最初は次を追加するのがよい。

```text
DkMath/Lib/Cosmic/GTail.lean
```

そして必要なら

```lean
-- DkMath/Lib/Basic.lean
import DkMath.Lib.Cosmic.GTail
```

ただし `Lib.Basic` が軽量入口なら、いきなり import してよいかは少し注意じゃ。
まずは `DkMath.Lib.Cosmic.GTail` 単体 build を通すのが優先。

## 7. build 順

この順がよい。

```bash
lake build DkMath.Lib.Cosmic.GTail
lake build DkMath.CosmicFormula.GTail
lake build DkMath.CosmicFormula.Defs
lake build DkMath.CosmicFormula
```

第一段階で全体 `DkMath` まで通す必要はない。
ただし最後に影響確認として、

```bash
lake build DkMath
```

をやる価値はある。

## 8. 今回の最初の commit 方針

commit 名はこれでよい。

```text
Add Lib cosmic GTail core
```

変更内容:

```text
- Add DkMath/Lib/Cosmic/GTail.lean
- Move pure algebraic GTail definitions and lemmas from CosmicFormula/GTail
- Keep CosmicFormula/GTail as downstream wrapper for Nat/padic/congruence lemmas
- Preserve namespace DkMath.CosmicFormula for compatibility
```

History にはこう書ける。

```md
## 2026/05/01 JST - Start GTail-centered Lib promotion

Started the GNZC Lib promotion from the general tail kernel.

- Added `DkMath.Lib.Cosmic.GTail`
- Moved the pure algebraic core of `GTail`
- Kept the public namespace `DkMath.CosmicFormula` for compatibility
- Left Nat / congruence / p-adic lemmas in `DkMath.CosmicFormula.GTail`
- This establishes `GTail` as the upstream core for `GN`, `GZ`, and future `GC`
```

## 9. この一手の意味

この作業で、DkMath の構造はこう変わる。

```text
Before:
CosmicFormula.GTail
  ├─ pure algebra
  ├─ Nat divisibility
  ├─ congruence
  └─ padicValNat

After:
Lib.Cosmic.GTail
  └─ pure algebra core

CosmicFormula.GTail
  ├─ Nat divisibility
  ├─ congruence
  └─ padicValNat
```

つまり、**GTail が本当に Lib の背骨になる** 。

そして次に、

```text
DkMath.Lib.Cosmic.GN
DkMath.Lib.Cosmic.GZ
DkMath.Lib.Cosmic.GC
```

を順に生やせる。

## 10. 賢狼の最終判断

始点はこれでよい。

```text
DkMath.Lib.Cosmic.GTail
```

しかも namespace は安全のため、

```lean
namespace DkMath.CosmicFormula
```

のままがよい。

第一波では **純代数 Tail のみ** 。
Nat / ModEq / p-adic はまだ動かさない。
`GN` は次段で `DkMath.Lib.Cosmic.GN` に切り出す。

これで、DkMath の GNZC 幹線は

\[
GTail \longrightarrow GN \longrightarrow GZ \longrightarrow GC
\]

という形で、ようやく根から固定され始める。
ふふん、良い船出じゃ。賢狼も少し胸が躍るのう。
