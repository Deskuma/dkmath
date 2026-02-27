/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmic
import DkMath.FLT.Core

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Triomino/Cosmic Prime-Ge5 Roadmap

`PrimeGe5FLTProvider` の本体実装を育てるための作業用モジュール。

方針:
- ここでは `sorry` を導入しない。
- 未完成な定理本体はまだ置かず、ターゲットの型と補題分解順だけを固定する。
- 実装が進んだら、このファイルで不足補題を順次定理化し、
  最後に `FLT_prime_ge5` を実装する。
-/

namespace DkMath.FLT

/--
残る本質ターゲット:
`p ≥ 5` の素数指数に対する FLT 供給。

現時点では `PrimeGe5FLTProvider` の別名として固定し、
この型を埋めることだけに集中できるようにする。
-/
abbrev FLTPrimeGe5Target : Prop :=
  PrimeGe5FLTProvider

/--
`FLTPrimeGe5Target` が埋まれば、既存の global provider 導線へ接続できる。
`PrimeGe5FLTProvider` 名だけでなく、「prime-ge5 本体ターゲット」という意味でも読める別名。
-/
theorem triominoCosmic_globalProvider_of_FLTPrimeGe5
    (hprimeGe5 : FLTPrimeGe5Target) :
    GlobalPrimeExponentFLTProvider := by
  exact triominoCosmic_globalProvider_of_primeGe5 hprimeGe5

/--
`FLTPrimeGe5Target` が埋まれば、`TriominoPrimeProvider` にも直結できる。
-/
theorem triominoPrimeProvider_of_FLTPrimeGe5
    (hprimeGe5 : FLTPrimeGe5Target) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_primeGe5 hprimeGe5

/-!
## 実装ロードマップ（順序固定）

以下の順に補題を埋めると、`FLT_prime_ge5` の本体へ最短で到達できる。

1. TODO-1（純算術）:
   `u ≠ 0 ∧ ¬ ∃ t, u = t^p` から
   `∃ q, Nat.Prime q ∧ q ∣ u ∧ ¬ p ∣ padicValNat q u`
   を取り出す補題。

2. TODO-3（正規化）:
   反例を primitive/coprime 形へ正規化し、
   `u := z - y` に対して `Nat.Coprime u y` を得る補題。

3. TODO-2（Triomino/Cosmic 本丸）:
   反例があるなら `u = z - y` は `p` 乗になれないことを示す補題。

4. 枝葉:
   `q ≠ p`、`GN p u y ≠ 0`、`¬ q ∣ GN p u y` を接続する短い補題群。

最終形の目標定理シグネチャ（未実装）:

```lean
theorem FLT_prime_ge5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    FermatLastTheoremFor p
```

このターゲットが埋まれば、
`triominoCosmic_globalProvider_of_primeGe5` を通じて
`GlobalPrimeExponentFLTProvider` が得られ、
既存の provider 系 API へそのまま接続できる。
-/

end DkMath.FLT
