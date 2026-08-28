# PUU-L010 — Square-Anchor Orbit / Wheel Reservation Projection

## 実装結果

`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit` を追加し、
`DkMath.NumberTheory.PrimorialUniverse` から公開した。

主な API は次のとおり。

- `squareAnchorWheelProjection S n := primeBasisWheelProjection S (n ^ 2)`
- `squareShellWheelProjection S n r := primeBasisWheelProjection S (n ^ 2 + r)`
- `squareShellWheelProjection_eq_anchor_add`
- `squareAnchorWheelProjection_succ`
- `squareAnchorWheelProjection_add_mul_period`
- `squareShellWheelProjection_add_mul_period`
- `reservedByPrimeBasis_projection_iff`
- `not_reservedByPrimeBasis_projection_iff`
- `not_reserved_iff_projection_wheelSurvivor`
- `squareShell_not_reserved_iff_projection_survivor`
- `primeBasisWheelProjection_insert_fresh_then_old`
- `squareShellWheelProjection_insert_fresh_projects_old`

公開定理とモジュール docstring を整備し、provider-side の有限算術 API である
こと、および Legendre 層から独立していることを明記した。

## Square-anchor の有限軌道

shell の座標は、anchor 座標に offset を加えてから旧周期で還元したものと一致する。
また、連続する square anchor について

```text
(n + 1)^2 = n^2 + (2*n + 1)
```

を用い、`2*n + 1` による厳密な更新則を証明した。

anchor を `k * finitePrimeBasisProduct S` だけ平行移動しても square projection は
不変であり、固定 shell offset についても同じ周期性を証明した。したがって、ここで
の orbit は有限 wheel period 上の自然な modulo 軌道として扱われる。

## Reservation と survivor の射影

PUU-L005 の周期性を商・剰余分解と組み合わせ、任意の自然数 `x` について

```text
ReservedByPrimeBasis S (projection S x)
  ↔ ReservedByPrimeBasis S x
```

を証明した。非予約側の同値も公開している。

`S.Nonempty` のとき、零剰余は基底中の任意の素数に予約されるため、非予約点の射影は
正であり、旧周期より小さい。これにより

```text
¬ ReservedByPrimeBasis S x
  ↔ IsPrimeBasisWheelSurvivor S (projection S x)
```

を得た。square shell についても同じ同値を specialization として公開した。
ここで `survivor` は有限基底に対する非予約点を意味し、素数性は主張していない。

## Nested-wheel coherence

fresh prime `q` による拡大 period が旧 period の倍数であることから、

```text
projection S (projection (insert q S) x) = projection S x
```

を証明した。square shell に適用した corollary も追加し、shell point が survivor
であることを仮定せずに、`6 → 30` の nested modulo coherence を扱えるようにした。

## `n = 4`, `6 → 30` 回帰

`S = {2, 3}` では `M = 6` であり、次を証明した。

```text
4^2 = 16
16 mod 6 = 4
4^2 + 1 = 17
17 mod 6 = 5
```

さらに `S = {2, 3, 5}` では `M' = 30` として

```text
17 mod 30 = 17
17 mod 6 = 5
```

を確認し、30-wheel を経由した旧 wheel への射影が直接の 6-modulo 射影と一致する
ことを回帰として残した。

## Semantic boundary

PUU-L010 は有限 wheel 上の square-anchor / square-shell projection と予約判定の
provider-side 構造に限定される。`DkMath.NumberTheory.Legendre` には依存せず、
`SquareOffset`、`SquareOffsetCovered`、Legendre conjecture、square-hole propagation、
full wheel-gap recursion、Euler-phi 同定、PowerSwap、GN/CosmicFormula、PNT/RH は
導入していない。

特に、非予約 square-shell point が素数であることは証明していない。このモジュールの
出力は、後続の Legendre consumer が利用する有限 projection / reservation API である。
