# Ultra-001B Report — Joint pressure and direct bridge

Date: 2026-07-26  
Status: **deterministic transport complete**

## 実装

```lean
GNOddPrimeJointPressureBudgetAffine
GNNonExceptionalChannelMassBudgetAffine
GNOddPrimeJointPressureBudgetAffine.of_liftGrowth_and_nonExceptional
Triple.log_c_mul_pred_le_of_oddPrime_jointPressure
Triple.abc_bound_of_oddPrime_jointPressure
ABCGNOddPrimeJointContract
abc_positive_of_GNOddPrimeJointContract
abc_of_GNOddPrimeJointContract
```

joint predicate は:

```text
L + E <= (1 + ρ) R + C
```

である。既存の separate lift-growth / non-exceptional-excess budget は
compatibility theorem により joint budget を供給するが、direct height bridge
は joint predicate を再分解しない。

## Direct bridge

```text
(p - 1) log c
  <= ρ log(rad(a*b*c)) + C + log(rad p)
```

margin:

```text
ρ <= (p - 1)(1 + ε)
```

から pointwise ABC bound を得る。

## Raw endpoints

`abc_of_GNOddPrimeJointContract` は:

```text
a = 0
b = 0
0 < a and 0 < b
```

を分離し、公開 `abc_main` と同じ raw-variable statement まで輸送する。
zero-coordinate case は coprimality から非零座標と `c` が `1` になる。

## 未完了部分

本 checkpoint は uniform `jointBudget` を構成していない。従って
`abc_main_axiom` を除去したという主張ではない。
