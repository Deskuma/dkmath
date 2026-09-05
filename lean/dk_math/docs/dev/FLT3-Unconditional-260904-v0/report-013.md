# FLT3U-013 実装報告: Well-Founded Closure of Primitive FLT3

## 実装範囲

`instruction-013` の FLT3U-010 checkpoint を実装した。U012 の
`exists_smaller_primitiveCubicPack` を product measure に対する
`Nat.strong_induction_on` に接続し、primitive positive coprime cubic solution を
矛盾化する production theorem を追加した。

arbitrary positive triple の gcd normalization、`fermatThree_no_positive_solution`、
`DkMath.FLT.Main` の変更、public aggregator、`NoSqOnS0` の変更はこの checkpoint の
非対象である。

## 追加 module と direct import

[PrimitiveCubicClosure.lean](../../../DkMath/FLT/Three/PrimitiveCubicClosure.lean)
を追加した。direct import は次の一つだけである。

```text
import DkMath.FLT.Three.PrimitiveCubicDescent
```

## Strong induction

`primitiveCubicPack_false` は次の補助命題を `n` に対して強帰納法で証明する。

```text
noAt : ∀ n : ℕ, ∀ {a b c : ℕ},
  PrimitiveCubicPack a b c → a * b * c = n → False
```

各 `p : PrimitiveCubicPack a b c` に対して
`exists_smaller_primitiveCubicPack p` を適用し、得られた `next` について

```text
x * y * z < a * b * c = n
```

を再帰 measure として `ih (x*y*z)` に渡す。packet の構造再帰は行わず、唯一の
再帰軸は自然数 measure `a*b*c` である。

strict decrease の source は U012 の
`PrimitiveCubicStrictDescent.measure_lt`、さらにその内部では U011 の
`EisensteinSignedCubeFactors.strict_product_lt` である。

## Public primitive endpoint

次の theorem を追加した。

```text
theorem FLT_d3_unconditional
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : Nat.Coprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

証明は hypotheses から `primitiveCubicPack` を構成し、
`primitiveCubicPack_false` に渡すだけである。この endpoint に
`hS0_not_sq`、`NoSqOnS0`、NoSqOnS0 provider、completed Mathlib FLT3 theorem は
現れない。

## Independence audit

新規 source と U013 の compiled import artifact を対象に、次を監査した。

- `DkMath.FLT.Main.FLT_d3_by_padicValNat` への参照なし
- `DkMath.FLT.Main`、`DkMath.FLT.Basic`、`DkMath.FLT.Core`、
  `DkMath.FLT.GEisensteinBridge` の production source import なし
- `DkMath.FLT.Five.*`、`DkMath.FLT.Seven.*` の production import なし
- `FermatLastTheoremThree`、`fermatThree_no_positive_solution`、
  `hS0_not_sq`、`NoSqOnS0` の参照なし
- `sorry`、`axiom`、completed FLT3 theorem shortcut の新規追加なし

既存 `DkMath.Basic` の広域 `import Mathlib` により、Lean の生成された全体
import-artifact には `Mathlib.NumberTheory.FLT.Three` も含まれる。ただしこれは
今回の module の明示的 import でも、production source 上の FLT3 theorem dependency
でもない。これを除去するには U013 の範囲を越える既存 `DkMath.Basic` の import
分解が必要になるため、ここでは変更していない。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.PrimitiveCubicClosure
```

focused build は `Build completed successfully (8722 jobs).` で終了した。新規
module 自身の warning はない。依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は
継続しているが、今回の module に新しい `sorry` はない。

主要 theorem の `#print axioms` は次の通りである。

```text
primitiveCubicPack_false:
  [propext, Classical.choice, Quot.sound]

FLT_d3_unconditional:
  [propext, Classical.choice, Quot.sound]
```

`sorryAx`、project-specific axiom、外部 completed FLT3 theorem axiom はない。

## Outcome

- Outcome A: selected。product measure 上の strong induction により、すべての
  `PrimitiveCubicPack a b c` を矛盾化し、`FLT_d3_unconditional` を kernel-checked
  に得た。
- Outcome B: selected ではない。今回の closure に formal obstruction は確認され
  なかった。
- Outcome C: selected ではない。route saturation による停止判定は発生していない。

残る U011 task は、任意の positive `a,b,c` の仮想解を共通 gcd で primitive な
`a',b',c'` に正規化し、この primitive endpoint を使って
`fermatThree_no_positive_solution` を public surface に公開することである。
