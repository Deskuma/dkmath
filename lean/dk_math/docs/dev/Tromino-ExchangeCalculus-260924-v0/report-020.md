# TRM-021 実装報告 — SimpleGraph / Dart / Coloring bridge

## region SimpleGraph

`DkMath/Tromino/GraphColoringBridge.lean` を追加した。
`regionCrossingRel C r s` を

```text
exists p, p.1 = r ∧ (C.cross p).1 = s
```

で定義し、`SimpleGraph.fromRel` により
`regionSimpleGraph C` を構成した。

crossingのinvolutionにより、fromRelが加える逆向き関係も元のport witnessに
戻せることを証明し、次の完全な隣接特徴付けを追加した。

```text
(regionSimpleGraph C).Adj r s ↔
  exists p, p.1 = r ∧ (C.cross p).1 = s
```

各portからの隣接生成と、`C.changesRegion`に基づくloop禁止も含む。

## Dart bridge

`flowPortToDart C p` を、source/target pairと上記隣接証明から定義した。
fst/sndのobserver theorem、全Dartが元のFlowNetworkPort witnessを持つ定理、
および次の reversal theoremを証明した。

```text
flowPortToDart C (reverseEdge C p)
  = (flowPortToDart C p).symm
```

さらに `Dart.edge` が反転で不変であることも確認した。

SimpleGraphはparallel edgeを保持しないため、portからDartへの写像は一般に単射ではない。
監査では2-region A A fixtureの異なる2 portが同一Dartに写ることを明示した。
これは情報損失の境界であり、FlowNetworkPortとのbijectionは主張していない。

## RegionPotentialからMathlib Coloring

`RegionPotential.toColoring` を `SimpleGraph.Coloring.mk` で定義した。
隣接のport witnessと `regionPotential_adjacent_ne` によりpropernessを証明し、
color値が `P.state` と一致するsimp theoremを追加した。

`card_state`を再利用して `Fintype.card TrominoState = 4` を得て、
potentialから `SimpleGraph.Colorable 4` を導出した。
edge-label recoveryもColoring上の薄いcorollaryとして公開した。

## zero holonomyからの標準coloring

rooted reachabilityとzero holonomyからTRM-020のpotential存在定理を適用し、
`(regionSimpleGraph C).Coloring TrominoState` と
`(regionSimpleGraph C).Colorable 4` を得る定理を追加した。

これは supplied FlowNetwork/FlowCrossing certificateに対する標準SimpleGraphの
proper four-state coloringであり、任意のplanar graphにそのcertificateが存在することや、
Four-Color theoremを主張するものではない。

## Audit / validation

`DkMathTest/Tromino/GraphColoringBridgeAxiomAudit.lean` を追加した。監査項目は、

- 2-region adjacencyとport witness
- port-to-Dartのfst/snd
- crossing/reverseと`Dart.symm`
- Dart edgeの反転不変性
- 全Dartのport witness
- parallel portの非単射性
- explicit RegionPotentialのColoring値 `0` / `deltaA`
- adjacency上のdistinct color
- `Colorable 4`
- RegionPotential-derived edge-label recovery
- 3-region odd-holonomy fixtureでpotential recoveryが不可能であること

次のbuildは成功した。

    lake build DkMath.Tromino.RegionPotential
    lake build DkMath.Tromino.GraphColoringBridge
    lake build DkMathTest.Tromino.GraphColoringBridgeAxiomAudit
    lake build DkMathTest.Tromino.RegionPotentialAxiomAudit
    lake build DkMathTest.Tromino.RegionWalkAxiomAudit

axiom auditでは、SimpleGraph/Dartの構造証明は `propext` と `Quot.sound` の範囲、
potential recoveryを通るcolorable theoremはTRM-020由来の
`Classical.choice`も含むことを確認した。新規production codeに `sorry`、`admit`、
`unsafe`、`axiom`、`noncomputable`は追加していない。

## Mathlib planarity boundary

本checkpointではMathlibのSimpleGraph、Dart、Walk/Coloring基盤のみを使用した。
repositoryで使用したMathlib API範囲には、任意のplanar embeddingやrotation-systemを
直接与える標準objectは確認できなかった。そのためplanar layerはDkMathの
combinatorial-map / rotation-system certificateとして別checkpointで扱う。

## 停止境界

planar embedding、rotation system、face extraction、open residual paths、ghost completion、
BoundaryIR、optimization、Four-Color theorem claimは実装していない。
