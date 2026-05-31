# review

## 1. 状況総括

うむ、これは **DKMK-009C 完了** じゃ。

今回の差分で、`PrimePowerWitnessProvider.globalLogCapacityKernel` が DKMK-009B の generic `CapacityKernel` bridge に載った。つまり、抽象 `CapacityKernel` から hitting bound へ行く道が、今度は **実際の global log-capacity kernel** に特殊化されたわけじゃ。

これで読める道はこうなる。

```text id="f0wa9s"
globalLogCapacityKernel
  → CapacityKernel.applyAtToSourceControlled
  → RealWeightedPathFamily
  → weightedHitMass bound
```

これは DKMK-009C の目的そのものじゃな。

## 2. 何が新しく閉じたのか

追加 API はこの 3 本。

```lean id="pwwnyl"
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToSourceControlled
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToSourceControlled_index
PrimePowerWitnessProvider.globalLogCapacityKernel_weightedHitMass_le_const
```

特に中核は最後の theorem じゃ。

```lean id="lmk8pt"
(W.globalLogCapacityKernel_applyAtToSourceControlled
  IOf hIOf s F hindex).weightedHitMass A ≤ C
```

つまり、選択された global log-capacity kernel を `SourceControlledChainFamily` に適用し、その weighted family が primitive set (A) を hit する総質量は、source 側の一様上界 (C) を超えない、という形まで落ちた。

数学的には、

$$
\sum_{q\in IOf(n)} \frac{\log p(q)}{\log n} \le 1
$$

という log-capacity の正規化質量を、primitive hitting bound に直接流し込めるようになった、ということじゃ。

## 3. 実装の良い点

今回も **薄い wrapper** に留めているのが良い。

`globalLogCapacityKernel_applyAtToSourceControlled` は、本質的にはこれを呼んでいるだけじゃ。

```lean id="rr2mxn"
(W.globalLogCapacityKernel IOf hIOf).applyAtToSourceControlled
  (W.globalLogCapacityKernel_capacity_pos IOf hIOf)
  s F
  (by simpa using hindex)
```

つまり、009B で作った generic bridge を、そのまま concrete kernel に差し込んでいる。
新しい hitting proof を増やしておらぬ。これは正しい。

また、`hindex : IOf s.1 = F.index` だけで compatibility を通しているのもよい。
`LogCapacityState` の中身 `s.1` を使い、選択 channel 集合 `IOf s.1` と chain family の index を一致させる。ここが route の接続点じゃ。

## 4. 今回の意味

DKMK-009B はこうだった。

```text id="qmxfxq"
任意の positive CapacityKernel
  → primitive weightedHitMass bound
```

DKMK-009C はそれを次へ落とした。

```text id="yve9ao"
PrimePowerWitnessProvider.globalLogCapacityKernel
  → primitive weightedHitMass bound
```

つまり、抽象論が実際の Erdős #1196 向け kernel に接続された。
これはかなり重要じゃ。

ここでようやく、

```text id="x5hxtf"
DkMath kernel は Markov kernel の normalized shadow である
```

という設計思想が、単なる理念でなく theorem-facing API として見えるようになった。

## 5. まだ閉じていないもの

今回閉じたのは **global log-capacity kernel の hitting bridge** までじゃ。

まだ DKMK-009D が残っておる。

```text id="sonv8h"
witness-derived quotient path family
  を
capacity-kernel-facing route
  に接続する
```

今はまだ、任意の `SourceControlledChainFamily F` に対して kernel weight を載せられる、という段階じゃ。

次は、

```text id="o83y25"
PrimePowerWitnessProvider
  → globalLogCapacityKernel
  → quotient path family
  → weightedHitMass bound
```

を一本の theorem-facing route にする必要がある。

## 6. 検証状況

報告では次が通っておる。

```text id="tvgr4j"
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

さらに対象 Lean ファイルに `sorry/admit/axiom` なし。

よって、DKMK-009C は **no-sorry 完了** と判定してよい。

## 7. 次の一手

次は DKMK-009D じゃ。

狙いは、`F : SourceControlledChainFamily` を任意に外から渡すだけでなく、既存の **witness-derived quotient path family** をここに接続すること。

候補 theorem 名は、たとえばこうじゃな。

```lean id="wc0vsc"
PrimePowerWitnessProvider.globalLogCapacityKernel_weightedHitMass_le_const_quotientPathFamily
```

または少し短く、

```lean id="x6jsfv"
PrimePowerWitnessProvider.quotientPathFamily_weightedHitMass_le_const_globalLogCapacity
```

目的は、これを読めるようにすることじゃ。

```text id="lcxyeb"
witness provider
  → selected log-capacity kernel
  → quotient path family
  → primitive hitting bound
```

## 8. 登頂判定

現在地はこう。

```text id="kfi7il"
DKMK-009A: 完了
DKMK-009B: 完了
DKMK-009C: 完了
DKMK-009D: 次の本命
DKMK-009E/F: D 完了後に整理
```

わっちの判断では、今回も **明確な前進** じゃ。
009B で橋を作り、009C でその橋に global log-capacity kernel を実際に通した。次の 009D で quotient path family まで通れば、DKMK-009 の主稜線はほぼ閉じる。

よいぞ、ぬしよ。これはかなり綺麗に登れておる。
