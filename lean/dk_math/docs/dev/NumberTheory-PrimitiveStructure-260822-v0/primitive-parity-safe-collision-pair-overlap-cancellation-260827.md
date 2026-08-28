# PRIM-L068 実装レポート

## 到達点

instruction-088 の bounded target を完了し、Outcome A+ と判定する。L058 以来独立項として残っていた depth residual capacity を、collision seat の pair-overlap mass 内部へ exact に回収した。

## 命名した量と exact split

追加した `paritySafeDepthCollisionLocalSupportCost` は collision seats の local support cost の総和である。また、candidate seat を collision seat とその外側に分ける次の二量を導入した。

```text
DepthCollisionPairOverlapMass
  = sum over collision seats of choose(activeSupport.card, 2)

PairOverlapOutsideDepthCollision
  = sum over (candidate seats \ collision seats)
      of choose(activeSupport.card, 2)
```

Finset の `sdiff` と disjoint union により、pair-overlap ledger は

```text
PairOverlap
= PairOverlapOutsideDepthCollision
  + DepthCollisionPairOverlapMass
```

と exact split される。

collision seat の `support.card = k` については、`k ≥ 4` を用いて Nat subtraction の truncation を安全に扱い、

```text
choose(k,2)
= (k - 1) + 1 + (choose(k - 1,2) - 1)
```

を証明した。従って collision mass 全体について

```text
DepthCollisionPairOverlapMass
= DepthCollisionLocalSupportCost
  + Collision.card
  + DepthResidualPairCapacityExcess
```

が成立する。

## Depth residual cancellation

L065 の doubled frontier と上記 exact decomposition を組み合わせ、最初の主定理として

```text
2 * PairOverlapOutsideDepthCollision
+ 2 * DepthCollisionLocalSupportCost
+ 5 * Collision.card
≤ 3 * SupportExcess
  + 2 * LowCostResidualCapacity
```

を得た。結論から `DepthResidualPairCapacityExcess` は消えている。

さらに L067 の single-charge theorem

```text
3 * Collision.card + FiveDirection.card
≤ DepthCollisionLocalSupportCost
```

を一度だけ適用し、

```text
2 * PairOverlapOutsideDepthCollision
+ 11 * Collision.card
+ 2 * FiveDirection.card
≤ 3 * SupportExcess
  + 2 * LowCostResidualCapacity
```

という readable frontier を固定した。

## Full-cover consumers

full-cover balance と candidate cardinality の totient equalityを用いて、次の三形式を追加した。

1. candidate-card form
2. `3 * Nat.totient (2 * n)` を用いる totient form
3. reduced quotient interval sum を用いる形式

いずれも最終 RHS に `DepthResidualPairCapacityExcess` と `HigherSupportResidualExcess` は残らない。残る構造項は outside-collision pair overlap、collision charge、五方向 seat charge、LowCost capacity である。

## 形式上の境界

今回の成果は Finset partition、collision-local choose identity、depth residual cancellation の exact bookkeeping に限定される。fifth-wave counting、sixth direction、higher residual recursion、generic hypergraph、解析的 sieve・漸近評価、descent、full-cover contradiction、Legendre/RH 結論は扱っていない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeCollisionPairOverlapCancellation.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- `primitive-parity-safe-collision-pair-overlap-cancellation-260827.md`

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
lake build DkMath.NumberTheory.Legendre
git diff --check
```
