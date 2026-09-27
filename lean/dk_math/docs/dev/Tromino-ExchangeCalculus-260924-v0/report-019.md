# TRM-020 実装報告 — Region potential reconstruction / label-only ColorRecovery kernel

## 実装範囲

`DkMath/Tromino/RegionPotential.lean` を追加した。定義は
`FlowNetwork` と `FlowCrossing` のみに依存し、`BoundaryContact`、
`FlowPairing`、`FlowTransition`を要求しない。

## RegionPotentialとwalk integration

`RegionPotential C` を、regionごとの `TrominoState` と

```text
state(target p) = state(source p) + flowEdgeLabel p
```

のedge lawを持つcertificateとして定義した。`FlowRegionWalk.Valid`の構造再帰により、
任意のwalkについて次を証明した。

```text
P.state s = P.state r + regionWalkXor W
```

nilおよびsingletonの積分形も公開した。

## zero holonomyと存在

potentialが存在すれば任意のclosed walkのXORがzeroになる
`regionPotential_regionZeroHolonomy`を証明した。これはpotentialの必要条件である。

`RootedRegionConnected C base` を定義し、rootから各regionへのwalkを
`Classical.choice`で選ぶ存在証明を追加した。選択walkのXORにrootの選択walkのXORを
加えて正規化することで、任意の `baseState` に対して

```text
RegionZeroHolonomy C ->
  exists P, P.state base = baseState
```

を証明した。production側にsolver-facingなnoncomputable定義は導入していない。

## 一意性とgauge

rooted connectivityの下でbase stateが一致する2つのpotentialのpointwise一意性を証明し、
potential extensionalityも追加した。

また、`translateRegionPotential gamma P` をcomputableに定義し、edge lawが保存されることを
証明した。任意の2 potentialについて、

```text
Q.state s = P.state s + (P.state base + Q.state base)
```

というglobal `TrominoState` translation gaugeを証明した。

## edge recoveryとproper-state separation

edge lawから

```text
P.state source + P.state target = flowEdgeLabel
```

を導出した。FlowSignatureのnonzero条件と合わせ、crossingのsource/targetのpotential値が
常に異なることを `regionPotential_adjacent_ne` と
`regionPotential_proper_on_crossing` として証明した。

さらに、rooted connectivityを仮定したzero-holonomyと、任意baseStateに合わせた
potential存在の同値を追加した。

## Audit / validation

`DkMathTest/Tromino/RegionPotentialAxiomAudit.lean` を追加した。監査対象は次のとおり。

- singletonおよびclosed walkのintegration
- potentialからzero holonomy
- zero holonomyとrooted reachabilityからの存在
- fixed baseでの一意性
- translationによるedge law保存
- global gauge relation
- edge-label round trip
- crossing endpointのdistinctness
- 明示的2-region positive fixture
- 3-region period-3 odd cycleのpotential不存在

2-region fixtureでは明示potentialからzero holonomyを証明してから再構成定理を適用した。
3-region fixtureではTRM-018/019の非zero period-3 XORとpotential由来zero holonomyを矛盾させた。

次のbuildは成功した。

    lake build DkMath.Tromino.RegionWalk
    lake build DkMath.Tromino.RegionPotential
    lake build DkMathTest.Tromino.RegionPotentialAxiomAudit
    lake build DkMath.Tromino.FlowTransitionXor
    lake build DkMathTest.Tromino.RegionWalkAxiomAudit

axiom auditでは存在構成と選択walkに `Classical.choice` が現れることを確認した。
その他は既存の有限構造・商に由来する `propext` と `Quot.sound` の範囲である。
新規production codeに `sorry`、`admit`、`unsafe`、`axiom`、`noncomputable`は追加していない。

## 停止境界

本checkpointで扱ったのは、supplied FlowNetwork/FlowCrossing上のlabel-only potential
reconstructionとproper four-state certificateである。これはFour-Color theoremの主張ではない。
planar-map extraction、open residual paths、ghost completion、BoundaryIR、optimization、
Four-Color theorem claimは実装していない。
