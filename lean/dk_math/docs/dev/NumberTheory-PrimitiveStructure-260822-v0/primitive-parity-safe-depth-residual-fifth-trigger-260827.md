# PRIM-L066 実装レポート

## 到達点

`ParitySafeDepthResidualFifthTrigger` を追加し、L065 の full-cover capacity frontier に現れる depth residual を、四方向 collision の固定 baseline と、support cardinality が 5 以上のときだけ現れる higher-support excess に exact 分解した。

主分解は次の通りである。

```text
DepthResidualPairCapacityExcess
= 2 * collisionSeats.card
  + HigherSupportResidualExcess
```

`HigherSupportResidualExcess` は `support.card ≥ 5` の collision seat に限って非零となる。従って、五方向 collision seat の Finset が空であることと higher-support residual が 0 であることも形式化した。

## 追加した API

- `paritySafeDepthResidualLocalCapacity_ge_two_of_collision`
- `paritySafeRechargeExactDepthHigherSupportResidualExcess`
- `paritySafeDepthResidualLocalCapacity_eq_two_add_higher`
- `paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_twoCollision_add_higherSupport`
- `paritySafeRechargeExactDepthFiveDirectionCollisionSeats`
- `paritySafeDepthHigherResidual_eq_zero_iff_support_card_eq_four`
- `paritySafeDepthHigherResidual_pos_iff_support_card_ge_five`
- `paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_fiveDirection_sum`
- `paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision`

さらに、L065 の frontier を次の形に sharpen した。

```text
2 * PairOverlap + 3 * totient(2*n)
≤ 3 * IncidenceCount
  + 2 * LowCostResidualCapacity
  + collisionSeats.card
  + 2 * HigherSupportResidualExcess
```

reduced quotient interval 形式と、五方向 collision が存在しない場合の corollary も追加した。

## 形式上の境界

今回の「五方向」は、`support.card ≥ 5` という residual の発火条件を分離した名前であり、五方向の新しい descent、counting、injectivity、residual recursion を構成するものではない。full-cover 仮定のない評価や新しい capacity estimate、Legendre の contradiction も導入していない。

したがって、今回の成果は raw structural term の exact bookkeeping と、L065 frontier 内で higher-support 部分が現れる場所の明示である。

## 検証

以下を実行し、対象 module と facade の build が成功した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger
lake build DkMath.NumberTheory.Legendre
```

Lean public facade `DkMath.NumberTheory.Legendre` に新 module の import も追加した。
