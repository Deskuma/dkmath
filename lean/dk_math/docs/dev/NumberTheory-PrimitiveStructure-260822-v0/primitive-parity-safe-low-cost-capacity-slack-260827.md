# PRIM-L069 実装レポート

## 到達点

instruction-089 の bounded target を完了し、Outcome A+ と判定する。L063/L064 で導入された三つの upper capacity と、L062 の actual LowCost residual mass の差を、名前付き `Nat` slack として exact に分解した。さらに L068 full-cover frontier を actual mass と明示的 slack の形へ rewrite し、required slack の有限必要条件を固定した。

## 三つの component slack

次の三量を定義した。

```text
NearWaveCapacitySlack
  = NearFirstPrimeWaveBudget - NearResidual.card

NonCollisionDepthCapacitySlack
  = PrimeSquareDepthBudget - NonCollisionDepth.card

FourthGateCapacitySlack
  = FourthGateDualBasePairs.card - ExactFourth.card
```

既存の三つの cardinal upper bound を用いて、各 capacity を

```text
capacity = actual branch mass + branch slack
```

とする exact identity を証明した。ここで `slack` の非負性は Nat subtraction と既存 upper bound によって表現されるが、slack がゼロであること自体は主張していない。

## Total decomposition と zero criterion

三つの slack の和

```text
LowCostResidualCapacitySlack
  = NearWaveCapacitySlack
  + NonCollisionDepthCapacitySlack
  + FourthGateCapacitySlack
```

を定義し、主定理

```text
LowCostResidualCapacity
  = LowCostResidualMass + LowCostResidualCapacitySlack
```

を exact equality として実装した。

また、total slack がゼロであることと、三 component slack がすべてゼロであることを同値化した。各 component の zero criterion と組み合わせることで、total slack がゼロであることは、三つの既存 upper bound がすべて equality になることと同値である。これは tightness の算術的判定だけであり、Near の injectivity、Fourth の set equality、または新しい構造補題を意味しない。

## L068 frontier の slack normal form

L068 の totient frontier を、次の actual-mass + slack 形式へ移した。

```text
2 * PairOverlapOutsideDepthCollision
+ 11 * Collision.card
+ 2 * FiveDirection.card
+ 3 * totient(2*n)
<=
3 * IncidenceCount
+ 2 * LowCostResidualMass
+ 2 * LowCostResidualCapacitySlack
```

さらに `IncidenceCount` を reduced quotient interval の有限和へ置換した consumer theorem も追加した。これは新しい estimate ではなく、L068 の capacity 項に L069 の exact decomposition を代入した bookkeeping である。

## Required slack frontier

左辺と

```text
3 * IncidenceCount + 2 * LowCostResidualMass
```

との差を `paritySafeFullCoverRequiredLowCostSlack` として定義した。full cover の仮定の下で

```text
FullCoverRequiredLowCostSlack
  <= 2 * LowCostResidualCapacitySlack
```

を証明した。従って、full cover を維持するためのこの有限 ledger gap は、三つの upper universe の overpayment によってのみ供給される。全 slack がゼロの場合の no-overpayment corollary も追加した。

## 形式上の境界

今回の実装は Finset cardinality upper bound、Nat subtraction、L068 frontier の rewrite に限定される。一般に `LowCostResidualCapacitySlack = 0`、各 component slack の消滅、`LowCostCapacity ≤ IncidenceCount`、または actual LowCost mass の outside-collision pair-overlap への包含は証明していない。Near の新しい wave counting、L018 budget の再評価、Fourth injectivity、fifth/sixth direction、higher-support recursion、解析的 estimate、descent、full-cover contradiction、Legendre/RH 結論も対象外である。

## 次 checkpoint への利用点

今後は `NearWaveCapacitySlack`、`NonCollisionDepthCapacitySlack`、`FourthGateCapacitySlack` を個別に比較できるため、LowCost capacity の overpayment がどの branch に集中しているかを、構造的 bottleneck として追跡できる。現時点ではどの slack がゼロになるとも仮定しない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeLowCostCapacitySlack.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- `primitive-parity-safe-low-cost-capacity-slack-260827.md`

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
lake build DkMath.NumberTheory.Legendre
```
