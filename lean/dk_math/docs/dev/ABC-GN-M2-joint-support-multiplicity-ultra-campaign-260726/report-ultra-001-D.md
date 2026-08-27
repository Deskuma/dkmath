# Ultra-001D Report — Finite valuation layer-cake

Date: 2026-07-26  
Status: **complete**

## 実装

Module:

```text
DkMath.ABC.GNDepthPressure
```

主要 API:

```lean
GNNonExceptionalDepthSupport
GNNonExceptionalDepthMass
GNNonExceptionalSupportLogMass
factorization_pred_mul_log_eq_sum_depths
GNNonExceptionalValuationExcess_eq_sum_prime_depths
GNNonExceptionalSupportLogMass_eq_log_product
```

各 non-exceptional support prime `q` について:

```text
(factorization q - 1) * log q
  =
sum over k in [2, factorization q] of log q
```

を有限和として証明した。従って non-exceptional excess は全 support prime の
高次 depth cell の有限総和である。

## Interpretation boundary

この identity は同じ `q` を depth ごとに再計上する。異なる depth が新しい
異なる prime を生成するという主張ではない。従って layer-cake 単独では
radical support を増加させない。
