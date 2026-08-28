# PRIM-L067 実装レポート

## 到達点

`ParitySafeFifthDirectionGate` を追加し、L066 の `support.card ≥ 5` trigger を、実際の第五素数方向・第五べき gate・support-cost ledger の追加 1 charge へ接続した。必須項目をすべて閉じたため、Outcome A+ と判定する。

## Actual fifth-prime packet

`paritySafeRechargeDepthFiveDirectionCollision_fiveDirection_packet` は、五方向 collision seat `r` から、canonical prime `p` と `q, s, u, v` を取り出す。

```text
p, q, s, u, v ∈ paritySafeActiveSupport n r
p < q, p < s, p < u, p < v
q,s,u,v は相互に異なる
p*q*s*u*v ∣ n^2 + r
```

`q, s, u` は L059 の既存 four-direction packet を再利用し、`v` は support cardinality が 5 以上であることから `{p,q,s,u}` の外側で選んだ。新しい generic tuple／hypergraph abstraction は導入していない。

## Fifth-power gate

`paritySafeFiveDirectionGatePrimes` を

```text
{ p ∈ squareAnchorOddActivePrimes n | p^5 < squareBody n }
```

として定義した。五方向 packet の product divisibility、点の正値性、square-body 上界、および `p < q,s,u,v` から

```text
p^5 < p*q*s*u*v ≤ n^2+r ≤ squareBody n
```

を示し、各五方向 collision の canonical prime がこの gate に入ることを形式化した。また `p^5` gate が既存の `p^4` gate の部分集合であることも示した。

さらに、L066 の global criterion と接続して

```text
HigherSupportResidualExcess > 0
  -> FiveDirectionCollisionSeats.Nonempty
  -> ∃ canonical p, p^5 < squareBody n
```

を Lean theorem として固定した。

## Extra support charge

五方向 seat では local support cost が少なくとも 4 なので、同じ local sum を二重に使わず、indicator を用いて

```text
3 * Collision.card + FiveDirection.card ≤ localSupportCost
```

を証明した。この結果を既存の terminal/collision disjoint-union ledger に組み込み、

```text
2 * TerminalKeys.card
+ 3 * Collision.card
+ FiveDirection.card
≤ SupportExcess
```

を得た。

## Sharpened full-cover frontier

full-cover 仮定の下で、L066 frontier を次のように sharpen した。

```text
2 * PairOverlap
+ FiveDirection.card
+ 3 * totient(2*n)
≤ 3 * IncidenceCount
  + 2 * LowCostResidualCapacity
  + Collision.card
  + 2 * HigherSupportResidualExcess
```

reduced quotient interval 形式も追加した。

## 形式上の境界

今回の成果は actual fifth direction と有限 `p^5` gate、および既存 support-cost ledger の追加 charge の形式化に限定される。fifth product-wave capacity、fifth-prime injectivity、seat/key reconstruction、sixth direction、residual recursion、descent、解析的評価、full-cover contradiction、Legendre/RH の結論は扱っていない。

## 変更箇所と検証

- `DkMath/NumberTheory/Legendre/ParitySafeFifthDirectionGate.lean`
- `DkMath/NumberTheory/Legendre.lean` に facade import を追加
- `primitive-parity-safe-fifth-direction-gate-260827.md`

検証済み:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate
lake build DkMath.NumberTheory.Legendre
```
