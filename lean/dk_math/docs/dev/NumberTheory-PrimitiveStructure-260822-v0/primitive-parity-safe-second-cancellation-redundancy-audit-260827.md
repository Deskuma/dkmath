# PRIM-L073 実装レポート

## 判定

instruction-093 の bounded audit target を完了し、Outcome A+ — ROUTE SATURATION PROVED と判定する。

L072 の second-cancellation frontier は、独立した full-cover obstruction ではなく、既存の terminal/collision support-charge ledger の再表現に還元された。したがって、pair/support residual-refinement route はこの frontier で構造的に完結しているが、contradiction pressure は生じない。

## Exact decompositions

追加した [ParitySafeSecondCancellationRedundancyAudit.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeSecondCancellationRedundancyAudit.lean:1) では、candidate seats を collision surface とその外側に分解し、次を exact に証明した。

```text
SupportExcess
  = OutsideSupportExcess + CollisionLocalSupportCost

ResidualPairMass
  = OutsideResidualPairMass + CollisionResidualPairMass

OutsidePairOverlap
  = OutsideSupportExcess + OutsideResidualPairMass
```

collision residual については、L070/L071 の実際の fiber 分解と slack realization を比較し、

```text
CollisionResidualPairMass
  = Collision.card + DepthFiberExcess + UnusedResidualPairMass
```

を exact に固定した。

L072 の LowCost identity と組み合わせることで、第一の audit target も閉じた。

```text
OutsideResidualPairMass
  = Terminal.card + LowCostResidualMassAfterUnused
```

従って、外側 pair-overlap は

```text
OutsidePairOverlap
  = OutsideSupportExcess
  + Terminal.card
  + LowCostResidualMassAfterUnused
```

となる。

## Terminal charge と reduced support charge

既存の terminal seat inclusion、terminal/collision seat disjointness、terminal support cost identity を使い、terminal charge を collision surface の外側へ局所化した。

```text
2 * TerminalKeys.card ≤ OutsideSupportExcess
```

また、既存 L067 charge

```text
3 * Collision.card + FiveDirection.card
  ≤ CollisionLocalSupportCost
```

を 3 倍して、次の full-cover 非依存 frontier を得た。

```text
2 * TerminalKeys.card
+ 9 * Collision.card
+ 3 * FiveDirection.card
≤ OutsideSupportExcess + 3 * CollisionLocalSupportCost
```

## Redundancy equivalence

L072 frontier と reduced support charge が、全ての `n` で同値であることを証明した。

```lean
paritySafeSecondCancellationFrontier_iff_reducedSupportCharge
```

さらに `hn : 0 < n` と `SquareOffsetsFullyCovered n` の下で、totient/full-cover frontier についても同じ reduced support charge と同値になることを証明した。

```lean
paritySafeFullCoverSecondCancellationFrontier_iff_reducedSupportCharge
```

従って、L072 frontier は既存 support charge から無条件に再構成できる冗長 frontier であり、独立 obstruction ではない。

## 形式上の境界と停止点

今回追加したのは finite exact decomposition、support-charge localization、および frontier equivalence のみである。Near counting、reduced quotient の大小評価、L018 budget の新評価、Fourth injectivity、fifth/sixth direction、higher-support recursion、generic hypergraph、analytic sieve、descent、full-cover contradiction、Legendre/RH 結論は扱っていない。

今回の判定により、L065--L072 の同一 pair/support ledger を次 checkpoint で細分化することはしない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeSecondCancellationRedundancyAudit.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- 本レポート

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeSecondCancellationRedundancyAudit
lake build DkMath.NumberTheory.Legendre
git diff --check
forbidden-construct audit: clean
trailing-whitespace audit: clean
```
