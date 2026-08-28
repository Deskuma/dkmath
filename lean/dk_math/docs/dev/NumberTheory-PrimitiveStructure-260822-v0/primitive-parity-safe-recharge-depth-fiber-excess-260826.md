# PRIM-L057 実装報告

## Outcome

Outcome A — PAID/UNPAID DEPTH LEDGER。

L056 の seat return と pair fiber ledger を用いて、exact depth mass を
「L018 が直接支払う occupied-seat mass」と「未払いの fiber multiplicity」に
正確に分離した。n=58 の actual depth-fiber collision witness も閉じた。
一般の collision-support card ≥ 4 は実装せず、A+ には進めていない。

## 実装した API

追加モジュール:

`DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess`

- `paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats`
  と card positivity により、occupied seat の fiber が nonempty であることを公開。
- `paritySafeRechargeExactDepthFiberExcess` を
  `∑ r ∈ DepthSeats, (fiber.card - 1)` として定義。
- `paritySafeRechargeExactDepthPairs_card_eq_seats_add_fiberExcess`:

  ```text
  ExactDepth.card = DepthSeats.card + DepthFiberExcess
  ```

- `paritySafeRechargeExactDepthFiberCollisionSeats` と
  `paritySafeRechargeExactDepthFiberExcess_eq_collision_sum` により、excess の
  支持を card ≥ 2 の occupied seats に限定。
- `paritySafeRechargeExactDepthFiberExcess_eq_zero_iff` により、excess zero と
  全 occupied fiber の singleton 性を同値化。
- residual mass を

  ```text
  Near + Terminal + DepthSeats + DepthFiberExcess + Fourth
  ```

  に再構成し、L018 budget を代入した upper consumer と
  `PrimePairOverlapCount` の strongly-preferred upper consumer を追加。
- `paritySafeRechargeExactDepthPairs_card_le_L018Depth_of_fiberExcess_eq_zero`
  により、zero-excess が Depth branch の L018 完全支払いの frontier であることを公開。

## n=58 actual collision

`paritySafeRechargeExactDepthFiber_collision_witness_58` を証明した。

```text
(15, 21) ∈ ExactDepth
(21, 15) ∈ ExactDepth
ExactSeat 58 15 21 = 101
ExactSeat 58 21 15 = 101
2 ≤ (DepthPairsAtSeat 58 101).card
```

各 pair について shell selector は 11、depth divisor は 3 であり、
既存の exact witness API から membership を構成している。これは fiber
uniqueness が一般には成立しないことの concrete witness である。

## 非目標・未実装

- `DepthFiberExcess = 0` の全 n での主張
- fiber card ≤ 1、無条件の `ExactDepth.card ≤ L018 budget`
- 一般 collision seat から active support card ≥ 4 への reconstruction theorem
- generic graph/hypergraph、valuation tower、fifth direction
- smaller anchor、descent、analytic estimate、global contradiction、Legendre/RH

## Docstring と validation

新規 module docstring、公開定義、主要 theorem に paid/unpaid ledger の意味と
fiber non-uniqueness の境界を記載した。

実行した検証:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` を監査した。
commit、push、CI は依頼範囲外のため実施していない。
