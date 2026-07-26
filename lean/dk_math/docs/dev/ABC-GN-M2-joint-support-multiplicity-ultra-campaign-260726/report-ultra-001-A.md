# Ultra-001A Report — Exact odd-prime accounting

Date: 2026-07-26  
Status: **complete**

## 実装

Module:

```text
DkMath.ABC.GNJointPressureOddPrime
```

主要 theorem:

```lean
Triple.log_GN_eq_log_rad_add_nonExceptionalExcess_of_oddPrime
Triple.log_GN_eq_log_exceptional_add_log_nonExceptional_add_excess
```

奇素数指数では M1 の exceptional excess zero を exact identity に代入し:

```text
log GN
  = log(rad GN) + non-exceptional excess
  = log(exceptional support product)
      + log(non-exceptional support product)
      + non-exceptional excess
```

を得た。

## 重要な境界

次は一般には偽である。

```text
log GN = log(rad p) + S + E
```

exceptional support は空であり得る。正しい exact term は
`log GNExceptionalSupportProduct` であり、`log(rad p)` への置換は上界でのみ
許される。

## 検証

```text
lake build DkMath.ABC.GNJointPressureOddPrime
Build completed successfully.
```

新規 axiom、`sorry`、`native_decide` は使用していない。
