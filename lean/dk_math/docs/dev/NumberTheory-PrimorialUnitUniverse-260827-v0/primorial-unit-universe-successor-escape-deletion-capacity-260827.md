# PUU-L013 — Successor Old-Basis Escape / Fresh-Threshold Deletion Capacity

## 実装結果

`DkMath.NumberTheory.Legendre.PrimorialWheelSuccessorEscape` を追加し、
`DkMath.NumberTheory.Legendre` facade から公開した。L012 の successor-shell
transition と projected-survivor dictionary を使い、old-basis escape の Finset、
prime threshold の削除容量、composite successor の集合等式を形式化した。
モジュール docstring と公開定理の docstring も整備した。

## Escape Finset

以下の二つの Finset を導入した。

- `successorOldBasisEscapingOffsets`
- `successorProjectedEscapingOffsets`

それぞれの membership theorem は次の意味を持つ。

```text
r ∈ successorOldBasisEscapingOffsets n
  ↔ SquareOffset (n+1) r ∧ ¬ SuccessorOldBasisReserved n r

r ∈ successorProjectedEscapingOffsets n
  ↔ SquareOffset (n+1) r ∧
     IsPrimeBasisWheelSurvivor (primeScalesUpTo (n+1))
       (squareShellWheelProjection (primeScalesUpTo (n+1)) (n+1) r)
```

既存の `escapingSquareOffsets` は再定義せず、successor transition に必要な
old-basis reservation と projected wheel presentation を別々に保持している。

## First threshold seat

`successorOldBasisReserved_firstThreshold` により、`2 ≤ n` と
`Nat.Prime (n + 1)` のもとで

```text
SuccessorOldBasisReserved n (n+1)
```

を証明した。証明では old basis に `2` が含まれることと、prime `n+1` が奇数で
あることを用い、

```text
(n+1)^2 + (n+1) = (n+1)(n+2)
```

の偶数性を示している。従って
`not_mem_successorOldBasisEscapingOffsets_firstThreshold` により、最初の
threshold seat `r = n+1` は old-basis escape ではない。

## Prime-threshold deletion identity

中心結果は
`successorProjectedEscapingOffsets_eq_erase_secondThreshold` である。
`2 ≤ n` と `Nat.Prime (n + 1)` のもとで、

```text
successorProjectedEscapingOffsets n
  = (successorOldBasisEscapingOffsets n).erase (2*(n+1))
```

となる。L012 の二つの threshold-covered offsets のうち、
`r = n+1` は既に old-reserved なので old-basis escape を削除できない。
したがって fresh prime が old-basis escape を削除できる候補は、最大でも
`r = 2*(n+1)` の一つだけである。

この等式は `2*(n+1)` が常に old-basis escape であることを主張しない。従って、
prime threshold が実際に一つ削除する場合と、削除しない場合の双方を正確に
含んでいる。

## Deletion capacity

- `successorOldBasisEscapingOffsets_card_le_projected_add_one`
- `successorProjectedEscapingOffsets_nonempty_of_two_le_oldEscapeCard`

erase の cardinality から

```text
oldEscape.card ≤ projectedEscape.card + 1
```

を得た。特に old-basis escape が少なくとも二つあれば、fresh threshold の後にも
projected successor escape が少なくとも一つ残る。

これは shifted window に二つの old-basis escape が存在することを証明する結果では
ない。あくまで、二つ存在すると仮定した場合の fresh-threshold deletion capacity
である。

## Composite successor

- `successorProjectedEscapingOffsets_eq_old_of_composite`
- `successorProjectedEscapingOffsets_nonempty_iff_old_of_composite`

`1 ≤ n` と `¬ Nat.Prime (n + 1)` のもとでは、L012 の composite projected-survivor
equivalence から

```text
successorProjectedEscapingOffsets n
  = successorOldBasisEscapingOffsets n
```

を得た。従って composite successor では old-basis escape の非空性と実際の
projected successor escape の非空性が同値である。

## 回帰

`successorEscapeDeletionRegression_four` は `n = 4`, `q = 5` について次を
確認する。

```text
5 ∉ successorOldBasisEscapingOffsets 4
10 ∈ successorOldBasisEscapingOffsets 4
10 ∉ successorProjectedEscapingOffsets 4
```

ここで `5` は first threshold seat として old-reserved、`10 = 2*5` は
old-basis escape だが fresh prime `5` によって削除される。集合レベルの回帰は
一般の prime-threshold erase theorem を経由している。

## 次の propagation frontier

本 checkpoint は shifted successor window に escape が存在することを証明していない。
残る provider 要件は次の通りである。

```text
composite successor:
  shifted successor window に ≥ 1 old-basis escape が必要

prime successor:
  shifted successor window に ≥ 2 old-basis escapes が必要
```

prime case で threshold prime が削除できる old escape は高々一つなので、二つの
old escapesがあれば一つが残る。しかし、その二つの存在自体は新しい問題であり、
旧 shell の full cover や Finset cardinality だけからは導入していない。

## Semantic boundary

Outcome A+ — SUCCESSOR ESCAPE DELETION CAPACITY FORMALIZED / PROVIDER FRONTIER SHARPENED

本 checkpoint では shifted-window escape の存在、full-cover propagation、
Jacobsthal/max-gap bound、full wheel-gap recursion、Legendre conjecture、PowerSwap、
GN/CosmicFormula、PNT/RH は導入していない。
