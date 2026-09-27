# TRM-019 実装報告 — General region walk / crossing holonomy

## 実装範囲

`DkMath/Tromino/RegionWalk.lean` を追加した。APIは
`N : FlowNetwork` と `C : FlowCrossing N` にのみ依存し、
`ClosedFlowNetwork` や `FlowPairing` を要求しない。

各 `FlowNetworkPort` をそのまま `List` に保持し、連続性を依存した
validity certificateで表現する `FlowRegionWalk C r s` を導入した。
したがって、同じregion間のparallel edgeもport単位で保持される。

## crossing edgeとwalk algebra

次を実装・証明した。

- `flowEdgeSource`, `flowEdgeTarget`, `flowEdgeLabel`
- `reverseEdge` と source/target交換、involution、label保存、source-target非一致
- 空walk、singleton、length、append、reverse
- appendの単位元・結合則、および `reverse (reverse W) = W`
- reverseでport列を反転し、各portをcrossingで戻す構造

## XOR holonomy

walk labelsの `List.sum` として `regionWalkXor` を定義し、nil、singleton、
append、reverseの恒等式を証明した。reverseで符号を導入せず、
`FlowCrossing.sameLabel` と `TrominoState` のcharacteristic-twoを使用している。

`ClosedRegionWalk` と network-level の `RegionZeroHolonomy` を追加し、
zero holonomyの下で同じendpointを持つ任意の2 walkのXORが一致することを証明した。
逆向きの局所的な含意として、同一endpointの全walk XOR一致から
`RegionZeroHolonomy`を得る定理も追加した。

## reachabilityとtransition bridge

`RegionReachable` を `Nonempty (FlowRegionWalk C r s)` として定義し、
反射・対称・推移を証明した。

`ClosedFlowNetwork`上では、`transitionRegionWalk N p n` を構成し、
endpointがtransition iterateのregionであること、lengthが `n` であること、
および

```text
regionWalkXor (transitionRegionWalk N p n)
  = flowTransitionXor N p n
```

を証明した。transition returnからclosed region walkを得て、
`RegionZeroHolonomy`がtransition XOR zeroを含意する定理と、primitive returnに
対するperiod evenの含意も追加した。

## Audit / validation

`DkMathTest/Tromino/RegionWalkAxiomAudit.lean` を追加した。監査では、2-regionの
往復closed walk、walkのreverse/append/XOR、reachable API、3-region period-3の
transition bridge、zero-holonomyからのzero XOR含意、および period-3で
`RegionZeroHolonomy`が成立しないことを確認した。

次のbuildは成功した。

    lake build DkMath.Tromino.RegionWalk
    lake build DkMathTest.Tromino.RegionWalkAxiomAudit

既存のaxiom auditと合わせ、依存axiomは有限集合・順序同型・商に由来する
`[propext, Classical.choice, Quot.sound]` の範囲である。新規production codeに
`sorry`、`admit`、`unsafe`、`axiom`、`noncomputable`は追加していない。

## 停止境界

本checkpointでは、zero holonomyからglobal potentialやglobal coloringを構成していない。
open residual path、ghost completion、planarity、BoundaryIR、optimization、
Four-Color theoremも実装していない。TRM-018のperiod-3 nonzero calibrationは
監査で維持した。
