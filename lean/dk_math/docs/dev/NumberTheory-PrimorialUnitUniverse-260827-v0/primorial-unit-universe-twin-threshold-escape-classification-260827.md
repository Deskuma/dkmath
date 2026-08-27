# PUU-L014 — Twin-Threshold Exception / Exact Old-Escape Classification

## 実装結果

`DkMath.NumberTheory.Legendre.PrimorialWheelTwinThreshold` を追加し、
`DkMath.NumberTheory.Legendre` facade から公開した。L013 の erase identity を
L011 の既存 Legendre escape vocabulary と接続し、prime threshold における
old-basis escape の唯一の例外を twin-prime 条件として分類した。
モジュール docstring と公開定理の docstring も整備した。

## Existing Legendre escape set との接続

`successorProjectedEscapingOffsets_eq_escapingSquareOffsets` により、`1 ≤ n` の
もとで

```text
successorProjectedEscapingOffsets n
  = escapingSquareOffsets (n + 1)
```

を証明した。これは projected wheel presentation と既存の Legendre consumer
vocabulary の同一視であり、`escapingSquareOffsets` の再定義は行っていない。

## Second threshold seat と twin prime

以下を実装した。

- `secondThreshold_not_oldReserved_iff_twinPrime`
- `secondThreshold_mem_oldEscape_iff_twinPrime`

`2 ≤ n` と `Nat.Prime (n + 1)` のもとで、

```text
¬ SuccessorOldBasisReserved n (2*(n+1))
  ↔ Nat.Prime (n+3)
```

および Finset membership 版を得た。基礎となる恒等式は

```text
(n+1)^2 + 2*(n+1) = (n+1)*(n+3)
```

である。

従って `n+3` が prime のときだけ、second threshold seat `2*(n+1)` は
old-basis escape となる。`n+3` が composite のときは、その prime divisor が
`primeScalesUpTo n` に戻り、seat は既に old-reserved である。

## Prime threshold の exact classification

`mem_successorProjectedEscapingOffsets_iff_old_ne_second` により、任意の offset
について

```text
r ∈ projectedEscape
  ↔ r ∈ oldEscape ∧ r ≠ 2*(n+1)
```

を得た。さらに `prime_of_mem_successorOldBasisEscape_ne_second` で、second seat
以外の old-basis escape は L011 の projected-survivor / square-shell primality
bridge を通じて successor shell の prime point になることを示した。

集合レベルでは
`successorOldBasisEscapingOffsets_eq_projected_union_twinSeat` により、

```text
oldEscape
  = projectedEscape
    ∪ (if Nat.Prime (n+3) then {2*(n+1)} else ∅)
```

を証明した。ここで `oldEscape.card ≥ 2` は一様な十分条件に過ぎず、すべての
prime-threshold case で必要条件だとは扱っていない。

## Exact nonemptiness frontier

`successorProjectedEscapingOffsets_nonempty_iff_exists_old_ne_second` により、

```text
projectedEscape.Nonempty
  ↔ ∃ r ∈ oldEscape, r ≠ 2*(n+1)
```

を得た。

さらに branch を分け、次を形式化した。

- twin-prime threshold (`Nat.Prime (n+3)`):
  `projectedEscape.Nonempty ↔ 2 ≤ oldEscape.card`
- non-twin prime threshold (`¬ Nat.Prime (n+3)`):
  `projectedEscape = oldEscape` および非空性の同値

従って L013 の「old escape が二つ以上」という条件は、twin-prime branch では
正確な条件になる一方、non-twin branch では一つの old escape で十分である。

## 回帰

`successorTwinThresholdRegression_four` は `n = 4`, `q = 5`, `q+2 = 7` に対し、

```text
5 は prime
7 は prime
10 ∈ successorOldBasisEscapingOffsets 4
10 ∉ successorProjectedEscapingOffsets 4
```

を確認する。`10 = 2*5` は twin-prime threshold の exceptional old escape であり、
fresh prime `5` によって削除される。

## Semantic boundary

本 checkpoint は shifted successor window に old escape が存在することを証明して
いない。残る provider は、prime successor では second seat を除く old escape、
composite successor では old escape そのものである。従って、残りの問題は明示的な
twin-prime semiprime exception を除いた通常の Legendre escaping-offset problem と
して整理された。

本 checkpoint では arbitrary `n` に対する escape cardinality の下界、square-hole
propagation、Jacobsthal/max-gap bound、full wheel-gap recursion、Legendre conjecture、
PowerSwap、GN/CosmicFormula、PNT/RH は導入していない。

Outcome A+ — TWIN-THRESHOLD EXCEPTION CLASSIFIED / OLD-ESCAPE FRONTIER EXACT
