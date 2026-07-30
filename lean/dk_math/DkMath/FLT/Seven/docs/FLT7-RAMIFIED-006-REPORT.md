# FLT7-RAMIFIED-006 実装レポート

## 判定

Phase A、B、C、および Phase D の receiver 定義までは Lean で完了した。
最終の cubic-gap 表示式には routing-cell 正規化が一つ残るため、総合判定は
Outcome C とする。

## 固定した事実

`TerminalPrimitiveRamifiedSummitPacket` は terminal carrier を common
summit と同時に保持し、次を証明する。

```text
carrierUnit = gapRoot * residualRoot
7 ∤ gapRoot
depth(root.snd) = 5
depth(endpoint gap) = 6
depth(cubic gap) = 6
```

さらに整数環で factor seven を消去した。

```text
root.snd * sndCore = 7^5 * gapRoot^7 * gapQuotient
```

## gcd ledger と routing

中心 polynomial identity

```text
sndCore = norm(root) * quartic(root) - 49 * root.snd^6
```

および root／endpoint primitivity から、設計で要求された五つの
coprimality theorem を証明した。その結果、

```lean
RamifiedSecondCoordinateRoutingPacket
```

が 2 x 3 board を保持する。

## compensation receiver

```lean
ramifiedCompensationCore :=
  gcd (natAbs root.snd) (natAbs gapQuotient)

RamifiedCubicGapSeventhShapeReceiver :=
  ∃ w, ramifiedCompensationCore * residualRoot = w^7
```

を実装した。`ramifiedCompensationCore = 1` なら、この receiver は
`residualRoot = 1` in `ZMod 49` を強制する。

## 正確な停止点

一般の `nonempty_coprimeTripleRouting` は九つの cell を供給するが、
その公開 contract は cell を gcd として定義していない。したがって
現在の board の `c13` を、独立に定義した
`gcd(|root.snd|,|gapQuotient|)` と同一視してはならない。

次に必要なのは次の二点を一つの canonical routing packet に固定する
正規化補題である。

```text
c13 = ramifiedCompensationCore
c12 = verticalGapRoot^7
```

これにより初めて、設計の最終式

```text
|R-L| = 7^6 * verticalGapRoot^7 *
  (ramifiedCompensationCore * residualRoot)
```

が無条件に導出される。ここでは DESCENT、整数七乗根、FLT7 終結を
主張しない。
