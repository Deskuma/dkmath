# PUU-L011 — Legendre Square-Offset / Primorial Wheel Bridge

## 実装結果

`DkMath.NumberTheory.Legendre.PrimorialWheelBridge` を追加し、
`DkMath.NumberTheory.Legendre` facade から公開した。依存方向は

```text
PrimorialUniverse.SquareAnchorOrbit
          ↓
Legendre.PrimorialWheelBridge
```

のままであり、`PrimorialUniverse` facade から Legendre への逆依存は追加していない。
モジュール docstring と公開定理の docstring も整備した。

## 公開 API

### Bounded-prime adapters

- `primeScalesUpTo_isFinitePrimeBasis`
- `primeScalesUpTo_nonempty_of_two_le`

`mem_primeScalesUpTo` を直接利用し、`primeScalesUpTo n` が有限 prime basis である
ことを証明した。`2 ≤ n` では witness `2` により非空性を得ている。

### Cover / reservation dictionary

- `squareOffsetCovered_iff_reservedByPrimeBasis`
- `not_squareOffsetCovered_iff_not_reservedByPrimeBasis`

既存の `SquareOffsetCovered` を再定義せず、

```text
SquareOffsetCovered n r
  ↔ ReservedByPrimeBasis (primeScalesUpTo n) (n^2 + r)
```

を定義展開だけで接続した。

### Projected survivor dictionary

- `not_squareOffsetCovered_iff_projection_survivor`
- `squareShell_not_reserved_iff_projection_survivor`（provider 側）を利用

`2 ≤ n` では `primeScalesUpTo n` が非空なので、PUU-L010 の非予約点と
projected wheel survivor の同値を適用できる。これは square-shell point 自体の
素数性を仮定しない辞書である。

### Square-shell primality

- `squareOffset_prime_iff_not_covered`
- `squareOffset_prime_iff_projection_survivor`

`SquareOffset n r` と `0 < n` のもとで、既存 Frontier の
`prime_of_squareAnchoredSupportEscape` と support-disjointness API を再利用し、

```text
Nat.Prime (n^2 + r) ↔ ¬ SquareOffsetCovered n r
```

を証明した。逆向きの `prime → ¬ covered` は、covering prime が prime point を
割る場合にその prime point 自身でなければならないことと、square cell の下限から
局所的に処理している。

したがって `2 ≤ n` の square cell 内では、prime と projected survivor が同値になる。
ただし一般の finite-basis survivor 全体が prime と同義になったわけではなく、
square-cell の幾何条件と `primeScalesUpTo n` の bounded basis がこの昇格を与える。

### Global reduction

- `legendreConjecture_iff_projectedWheelEscape_from_two`

`n ≥ 2` の projected-wheel escape を使う Legendre conjecture の同値な reduction を
実装した。逆向きでは `n = 1` を prime witness `2` で別処理している。この定理は
Legendre conjecture の証明ではなく、既存の conjecture と provider-side escape の
形式的な置換である。

## 回帰と境界

`primorialWheelBridge_four_one` で次を確認した。

```text
primeScalesUpTo 4 = {2, 3}
4^2 + 1 = 17
17 mod 6 = 5
5 は {2,3}-wheel survivor
17 は prime
```

また `primeScalesUpTo_one_empty_wheel_boundary` により、

```text
primeScalesUpTo 1 = ∅
finitePrimeBasisProduct (primeScalesUpTo 1) = 1
primeBasisWheelSurvivors (primeScalesUpTo 1) = ∅
```

を明示した。従って `n = 1` は単なる例外処理ではなく、現在の open-period wheel
survivor 表現における実在する empty-basis 境界である。

## Semantic boundary

この checkpoint は finite cover / reservation / projection の bridge と reduction
に限定される。square-hole propagation、full-cover contradiction、Jacobsthal または
gap bound、wheel-gap recursion、PowerSwap、GN/CosmicFormula、PNT/RH は導入していない。

特に、すべての square shell に escaping offset が存在すること、あるいは Legendre
conjecture 自体は証明していない。square-shell の非予約点が prime になるのは、
`SquareOffset` と bounded-prime support escape を通した局所的な同値である。
