# PUU-L009 — Nested Wheel Projection / Reflection Compatibility

## 実装結果

`DkMath.NumberTheory.PrimorialUniverse.WheelProjection` を追加し、facade
`DkMath.NumberTheory.PrimorialUniverse` から公開した。

主な API は次のとおり。

- `primeBasisWheelProjection S x := x % finitePrimeBasisProduct S`
- `primeBasisWheelProjection_lift`
- `enlargedWheelSurvivor_projects_to_oldSurvivor`
- `oldWheelSurvivor_has_enlargedLift`
- `primeBasisWheelProjectionFiber`
- `primeBasisWheelProjectionFiber_eq_liftImage`
- `card_primeBasisWheelProjectionFiber`
- `primeBasisWheelProjection_reflect_insert_fresh`

公開定理とモジュール docstring には、旧周期への canonical projection、
survivor の意味、およびこの checkpoint で扱わない構造を記載した。

## 証明の要点

`primeBasisWheelProjection_lift` は、`r < M` のもとで

```text
(r + j * M) % M = r
```

を直接示す左逆定理である。大域 survivor の射影については、PUU-L008 の
`enlargedWheelSurvivor_iff_exists_oldSurvivorLift` を再利用し、商・剰余で得られた
旧 survivor `r` と lift 表現から射影先を同定した。

各旧 survivor `r` に対して、PUU-L008 の
`freshPrimeSurvivingLiftIndices S q r` を witness fiber として用いた。この
Finset は fresh prime による唯一の削除を除いた lift index 集合であり、
`card_freshPrimeSurvivingLiftIndices` により `q - 1` 元である。素数 `q` の
`1 < q` から、この fiber の非空性と射影の全射性を得た。

さらに、projection fiber を

```text
(primeBasisWheelSurvivors (insert q S)).filter
  (fun x => primeBasisWheelProjection S x = r)
```

として定義し、これが `freshPrimeSurvivingLiftIndices` の lift image と一致する
ことを証明した。lift の旧座標・index に関する単射性により、fiber の cardinality
は正確に `q - 1` となる。

## Reflection compatibility

`M = finitePrimeBasisProduct S`、`M' = q * M` とし、拡大 survivor を

```text
x = r + j * M,  j < q
```

に分解した。`M' - x` を

```text
(q - (j + 1)) * M + (M - r)
```

と表して modulo `M` を取り、

```text
projection(M' - x) = M - projection(x)
```

を得た。したがって、拡大段階ごとに反射を作り直すのではなく、nested wheel
projection が既存の product-period reflection と整合する。

## `6 → 30` 回帰

旧 wheel `S = {2, 3}` の survivor は `{1, 5}`、fresh prime は `q = 5` である。
具体的な projection fiber を次のように証明した。

```text
projection = 1 : {1, 7, 13, 19}
projection = 5 : {11, 17, 23, 29}
```

各 fiber の cardinality は `4 = 5 - 1` である。これは enlarged wheel の 8 seats
が旧 wheel の 2 seats 上の 4-sheeted finite cover になることを明示する。

## 意図的に延期したもの

fresh-prime deletion によって隣接 gap が結合し得るため、同じ index の lift 差
以外の full gap-word transport はこの checkpoint に導入していない。gap-merging
法則、最大 gap、Jacobsthal bound、Euler-phi を主証明とする同定、square-anchor、
Legendre、PowerSwap、GN/CosmicFormula、PNT/RH は後続の境界に残した。

## Semantic boundary

PUU-L009 で確立した構造は、有限 wheel の nested quotient に限定される。

```text
fresh-prime enlargement
      ↓
enlarged survivor wheel
      ↓ modulo old period
old survivor wheel

surjective projection
constant fiber size q - 1
reflection-compatible
```

このモジュールは square-anchor や Legendre shell を仮定せず、survivor を素数と
同一視しない。
