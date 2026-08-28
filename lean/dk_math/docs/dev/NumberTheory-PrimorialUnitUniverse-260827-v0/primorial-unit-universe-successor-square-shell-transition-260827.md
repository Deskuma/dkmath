# PUU-L012 — Successor Square-Shell Transition / Fresh-Threshold Two-Seat Audit

## 実装結果

`DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor` を追加し、
`DkMath.NumberTheory.Legendre` facade から公開した。L011 の
`SquareOffsetCovered` / projected-survivor dictionary を再利用し、
successor shell の有限な遷移を prime/composite に分けて形式化した。
モジュール docstring と公開定理の docstring も整備した。

## 公開 API

### Bounded-prime basis transition

- `primeScalesUpTo_succ_eq`

`primeScalesUpTo (n + 1)` は、`n + 1` が prime の場合だけ
`insert (n + 1) (primeScalesUpTo n)` となり、composite の場合は旧 basis と
一致することを証明した。新しい prime enumeration API は導入していない。

### Old-basis view and shifted window

- `SuccessorOldBasisReserved`
- `successorOldBasisReserved_iff_shiftedOffset`
- `squareOffset_succ_shiftedOffset_range`

successor shell の旧 basis による reservation を

```text
SuccessorOldBasisReserved n r
  := ReservedByPrimeBasis (primeScalesUpTo n) ((n+1)^2 + r)
```

と定義し、anchor identity

```text
(n+1)^2 + r = n^2 + (2*n + 1 + r)
```

を定理化した。また `SquareOffset (n + 1) r` から shifted offset
`s = 2*n + 1 + r` が

```text
2*n + 2 ≤ s ≤ 4*n + 3
```

を満たすことを証明した。これは旧 shell の offset interval
`[1, 2*n]` とは別の window である。

### Exact cover transition

- `squareOffsetCovered_succ_iff_old_or_threshold`
- `successorThresholdPrime_dvd_iff`
- `squareOffsetCovered_succ_iff_threshold`
- `squareOffsetCovered_succ_iff_old_of_not_prime`

一般に successor coverage は

```text
SquareOffsetCovered (n+1) r
  ↔ SuccessorOldBasisReserved n r
     ∨ (Nat.Prime (n+1) ∧ (n+1) ∣ r)
```

となる。threshold prime の項では `(n+1)^2` の divisibility を消去している。
さらに `Nat.Prime (n + 1)` と `SquareOffset (n + 1) r` のもとで、threshold
prime が予約する offset はちょうど

```text
r = n + 1  または  r = 2 * (n + 1)
```

の二席であり、PUU-L007 の `q`-lift unique-deletion theorem とは異なる
successor-square-shell の有限幾何として扱っている。composite の場合は新しい
basis direction がないため、coverage は `SuccessorOldBasisReserved` と同値になる。

### Projected-survivor transition

- `successorProjectedSurvivor_iff_primeThreshold`
- `successorProjectedSurvivor_iff_composite`

L011 の
`not_squareOffsetCovered_iff_projection_survivor` を使い、prime threshold では

```text
projected survivor
  ↔ ¬ SuccessorOldBasisReserved n r
     ∧ r ≠ n+1 ∧ r ≠ 2*(n+1)
```

を得た。composite では

```text
projected survivor ↔ ¬ SuccessorOldBasisReserved n r
```

となる。composite の projected-survivor theorem には、L011 の非空 basis 条件を
満たすため `1 ≤ n` を明示している。

### Full-cover criterion

- `squareOffsetsFullyCovered_succ_iff_primeThreshold`
- `squareOffsetsFullyCovered_succ_iff_composite`

successor の full cover を、prime threshold の場合は「旧 basis reservation と
二つの threshold seat」、composite の場合は「旧 basis reservation」の全 offset
条件として、それぞれ必要十分条件にした。

## 回帰

`successorThresholdRegression_four_ten` は一般の threshold transition theorem を
使い、`n = 4` から prime successor `5` への具体例を確認する。

```text
primeScalesUpTo 4 = {2, 3}
primeScalesUpTo 5 = insert 5 (primeScalesUpTo 4)
5 ∣ 10
¬ SuccessorOldBasisReserved 4 10
SquareOffsetCovered 5 10
```

従って `r = 10 = 2 * 5` が、旧 basis による reservation ではなく新しい threshold
prime によって cover される二席の一つであることが、抽象定理を介して確認できる。

## Propagation frontier

旧 shell の full-cover 仮定が直接管理するのは

```text
n^2 + s,  1 ≤ s ≤ 2*n
```

である。一方、successor shell の old-basis reservation が必要とするのは

```text
n^2 + s,  2*n+2 ≤ s ≤ 4*n+3
```

である。従って、区間の cardinality や threshold seat の追加だけから
`SquareOffsetsFullyCovered n → SquareOffsetsFullyCovered (n + 1)` は導けない。
この間には、shifted window に reservation または survivor が現れることを保証する
新しい定理が残る。本 checkpoint はその exact transition を分解し、この
propagation frontier を明示した時点で完了とする。

## Semantic boundary

Outcome A+ — SUCCESSOR TRANSITION DECOMPOSED / PROPAGATION FRONTIER ISOLATED

本 checkpoint では Legendre の証明、square-hole propagation、Jacobsthal/max-gap
bound、full wheel-gap recursion、prime density、PowerSwap、GN/CosmicFormula、PNT/RH
は導入していない。
