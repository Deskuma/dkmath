# PRIM-L070 実装レポート

## 到達点

instruction-090 の bounded target を完了し、Outcome A+ と判定する。L069 の upper-capacity ledger には戻らず、L057/L062 の actual residual ledger と L068 の collision pair-overlap identity を組み合わせ、capacity-free full-cover frontier を追加した。

## Actual residual normal form

既存の exact residual identity と exact-depth seat の collision/noncollision split から、次を証明した。

```text
ResidualPairMass
  = LowCostResidualMass
  + Terminal.card
  + Collision.card
  + DepthFiberExcess
```

pair-overlap level でも、`SupportExcess` を先頭に置いた同じ actual normal form を public theorem として提供している。

## Collision residual-pair slack

次の global finite slack を定義した。

```text
CollisionResidualPairSlack
  = DepthResidualPairCapacityExcess - DepthFiberExcess
```

既存の `DepthFiberExcess ≤ DepthResidualPairCapacityExcess` を使い、

```text
DepthResidualPairCapacityExcess
  = DepthFiberExcess + CollisionResidualPairSlack
```

を exact equality として固定した。さらに slack=0 とこの upper bound の tightness の同値も追加したが、slack=0 自体は仮定・結論としていない。

## Collision mass と actual-fiber cancellation

L068 の collision mass decomposition を上の identity で rewrite し、

```text
CollisionPairOverlapMass
  = CollisionSupportCost
  + Collision.card
  + DepthFiberExcess
  + CollisionResidualPairSlack
```

を得た。

続いて L067 の strengthened support charge と pair-overlap split を適用した。`DepthFiberExcess` は左右から exact cancellation され、次の frontier が成立する。

```text
2 * OutsideCollisionPairOverlap
+ 2 * CollisionSupportCost
+ 3 * Collision.card
+ FiveDirection.card
+ 2 * CollisionResidualPairSlack
<=
3 * SupportExcess
+ 2 * LowCostResidualMass
```

さらに existing charge

```text
3 * Collision.card + FiveDirection.card
<= CollisionSupportCost
```

を一度だけ使い、capacity-free の readable form

```text
2 * OutsideCollisionPairOverlap
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 2 * CollisionResidualPairSlack
<=
3 * SupportExcess
+ 2 * LowCostResidualMass
```

を固定した。RHS に `LowCostResidualCapacity`、L069 の capacity slack、`DepthResidualPairCapacityExcess`、`DepthFiberExcess`、`HigherSupportResidualExcess` は残らない。

## Full-cover consumers

full-cover candidate balance を使った candidate-card form、candidate cardinality を `3 * Nat.totient (2 * n)` に置換した totient form、および `IncidenceCount` を reduced quotient interval の有限和に置換した form を追加した。最終的な reduced quotient form は

```text
2 * OutsideCollisionPairOverlap
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 2 * CollisionResidualPairSlack
+ 3 * totient(2*n)
<=
3 * ReducedQuotientIncidenceSum
+ 2 * LowCostResidualMass
```

である。

## L069 との役割差

L069 は `11C + 2F` という stronger collision coefficient を持つ代わりに、RHS に `2 * LowCostResidualCapacitySlack` を残す。一方 L070 は `9C + 3F + 2Q` となるが、RHS は actual LowCost mass のみである。`Q` と L069 の LowCost capacity slack の大小比較は今回行っていない。

## 形式上の境界

今回の成果は finite exact ledger と Nat arithmetic に限定される。`CollisionResidualPairSlack = 0`、L069 の capacity slack=0、Near wave の新 counting、L018 の新 estimate、Fourth injectivity、fifth/sixth direction の追加、residual recursion、descent、解析的 estimate、full-cover contradiction、Legendre/RH 結論は扱っていない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeActualFiberCancellation.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- `primitive-parity-safe-actual-fiber-cancellation-260827.md`

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
lake build DkMath.NumberTheory.Legendre
```
