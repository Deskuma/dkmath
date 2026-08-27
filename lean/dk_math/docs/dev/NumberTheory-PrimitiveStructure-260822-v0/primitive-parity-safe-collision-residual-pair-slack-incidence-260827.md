# PRIM-L071 実装レポート

## 到達点

instruction-091 の bounded target を完了し、Outcome A+ と判定する。L070 の抽象的な `CollisionResidualPairSlack` を、各 collision seat の canonical residual-pair target に対する未使用 image の cardinality sumとして exact に実現した。

## Fixed-seat image と unused pair

既存の L058 reverse-key map

```text
bt ↦ (paritySafeRechargeExactKeyOfPair n bt).2
```

を `paritySafeRechargeExactDepthResidualPairImageAtSeat` として Finset 化した。L058 の residual-pair membership と fixed-seat injectivity を用いて、

```text
ResidualPairImageAtSeat ⊆ CanonicalResidualPairsAtSeat
ImageAtSeat.card = ExactDepthPairsAtSeat.card
```

を証明した。

さらに target と image の差

```text
DepthCollisionUnusedResidualPairsAtSeat
  = CanonicalResidualPairsAtSeat \ ResidualPairImageAtSeat
```

を定義し、collision seat 上で

```text
UnusedResidualPairsAtSeat.card
  = choose(support.card - 1, 2) - ExactDepthPairsAtSeat.card
```

という local exact cardinality formula を得た。collision seat が covered candidate であることは、既存の occupied-fiber witness から回収している。

## Global realization of Q

local formula を collision seats 上で総和し、

```text
DepthResidualPairCapacityExcess
  = DepthFiberExcess + UnusedResidualPairMass
```

を exact equality として証明した。L070 の定義

```text
CollisionResidualPairSlack
  = DepthResidualPairCapacityExcess - DepthFiberExcess
```

と比較することで、今回の最重要 theorem

```text
CollisionResidualPairSlack
  = UnusedResidualPairMass
```

を固定した。

これは数値的な slack の再命名ではなく、既存 L058 injection の target に残った未使用有限 pair の質量による realization である。

## Zero saturation と positive witness

local unused Finset が空であることと、fiber image が canonical target を飽和することを同値化した。これを global identity と組み合わせ、

```text
CollisionResidualPairSlack = 0
```

が全 collision seat の image saturation と同値であることを証明した。また zero slack の下では、任意の canonical residual pair が exact-depth fiber の reverse image を持つことを direct surjectivity theorem として提供している。

反対に positive slack から、unused residual pair を持つ collision seat、さらに canonical target に属するが image に属さない具体的な pair の存在を取り出す theorem を追加した。この pair を新しい prime direction、fifth/sixth wave、descent などへ解釈することはしていない。

## L070 frontier の realized form

L070 の capacity-free frontier の abstract slack を unused residual-pair mass へ rewrite し、次を得た。

```text
2 * OutsideCollisionPairOverlap
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 2 * UnusedResidualPairMass
<=
3 * SupportExcess
+ 2 * LowCostResidualMass
```

full-cover candidate form、`3 * Nat.totient (2 * n)` を用いる totient form、reduced quotient interval sum の formも追加した。最終 RHS に upper capacity、L069 capacity slack、`DepthResidualPairCapacityExcess`、`DepthFiberExcess` は残らない。

## 形式上の境界

今回証明したのは fixed-seat finite image、local complement cardinality、global unused mass、zero saturation、positive unused-pair witness、および L070 frontier の rewrite だけである。unused pair から fresh/fifth/sixth prime、wave、descent、full-cover contradiction、Legendre/RH 結論は導いていない。L069 capacity slack との大小比較、Near の新 counting、L018 の新 estimate、Fourth injectivity、generic hypergraph abstraction も対象外である。

global `(seat, pair)` incidence Finset は、今回の目的に不要な dependent Finset complexityを避けるため追加していない。sum-of-cards realization で Outcome A+ の target を満たしている。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeCollisionResidualPairSlackIncidence.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- `primitive-parity-safe-collision-residual-pair-slack-incidence-260827.md`

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeCollisionResidualPairSlackIncidence
lake build DkMath.NumberTheory.Legendre
git diff --check
forbidden-construct audit: clean
trailing-whitespace audit: clean
```
