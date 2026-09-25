# TRM-022 実装報告 — rotation system / face-step kernel

## FlowLocalRotation

`DkMath/Tromino/RotationSystem.lean` を追加した。

`FlowLocalRotation N` は `FlowNetworkPort N` 上の `Equiv` と、rotationが
region indexを保存する証明からなる。rotationの逆写像と有限iterateについても
region保存を証明した。

各region内のportsに対する
`RegionRotationCyclic` と、それを全regionに要求する
`FlowRotationSystem` を定義した。これにより、同一region内の任意の二つの
portがrotation iterateで到達可能であることを表現する。

## crossing / face-step

`flowCrossEquiv` は `FlowCrossing.cross` と involution certificate を
equivalenceに包む。

face-stepは次の順序で固定した。

```text
alpha := crossing
rho   := local rotation
phi   := rho ∘ alpha
```

対応する `faceEquiv` の逆写像は `alpha ∘ rho⁻¹` であり、両方向の逆写像
identityをkernelで確認した。`faceStep_source` は一回のstepが、直前のcrossing
edgeのtargetから同じregionのportへ戻ることを示す。Dart bridgeについては
rotationがsource regionを保存することからendpoint equalityを追加した。

finite port set上の周期性を `faceStep_periodic` として導出し、
`FaceReturn`、`firstFaceReturn`、`FacePrimitiveReturn` と最小性・primitive性の
theoremを追加した。これは有限permutationの周期性であり、topological faceの
抽出ではない。

## 監査fixture

`DkMathTest/Tromino/RotationSystemAxiomAudit.lean` に、2 regions × 3 portsの
pure fixtureを追加した。crossingはregionを交換し、rotationは各region内の
3-cycleとした。監査では次をkernel-checkした。

- `FlowRotationSystem` のregion cyclicity
- crossing involutionとlocal rotationのregion保存
- face-stepの6-step return
- 一回ではreturnしないこと
- `faceStep_periodic` によるpositive period
- crossing edgeのsource/target endpoint relation
- Dart endpoint relation

さらに既存のclosed FlowNetworkに対して、rotationが
`flowLocalMatePort` と一致する場合に

```text
faceStep R N.crossing p = flowTransitionStep N p
```

となる条件付きcalibrationを監査した。

## 停止境界

本checkpointは有限port permutationとcombinatorial face-stepのkernelに限定した。
planar embedding、topological face quotient、Euler characteristic、genus、
noncrossing pairing、planarity判定、Four-Color theorem、またはuniversal rotation
providerは実装していない。`FlowRotationSystem` は supplied finite certificateで
あり、任意のFlowNetworkに自動的に存在することは主張していない。

## Audit / validation

次のbuildは成功した。

    lake build DkMath.Tromino.RotationSystem
    lake build DkMathTest.Tromino.RotationSystemAxiomAudit

監査の `#print axioms` では、新規rotation kernelの証明が
`propext`、`Quot.sound`、および有限性からの周期性・既存certificate由来の
`Classical.choice`の範囲にあることを確認した。新規production codeと監査fixtureに
`sorry`、`admit`、`unsafe`、`axiom`、`noncomputable`は追加していない。
