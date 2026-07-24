# Report 007: 二予算による ABC 最終合成

## 結果

Outcome A を達成した。新規 module は次である。

```text
DkMath/ABC/GNFinalBudgetBridge.lean
```

この checkpoint では、

```text
prime-support growth budget
+
valuation-multiplicity budget
  -> explicit K を持つ ABC bound
```

という最終合成を Lean theorem surface として固定した。

## valuation-excess budget

次の三つの affine budget predicate を定義した。

```text
GNValuationExcessBudgetAffine
GNExceptionalExcessBudgetAffine
GNNonExceptionalExcessBudgetAffine
```

いずれも ABC radical の対数に対する線形係数と加法定数を持つ。

既存の exact partition

```text
GNValuationExcess
  = GNExceptionalValuationExcess
  + GNNonExceptionalValuationExcess
```

から、次を証明した。

```text
GNValuationExcessBudgetAffine.of_split
```

exceptional budget `(τe, De)` と non-exceptional budget `(τn, Dn)` は、
full budget `(τe + τn, De + Dn)` に合成される。

有限個の exceptional prime support と、その prime 上の valuation depth
は区別している。`exceptional support product ∣ rad n` だけから
exceptional valuation multiplicity の一様上界は主張していない。

## support / excess の合流

次を証明した。

```text
Triple.log_c_mul_pred_le_of_support_and_excessBudget
```

証明経路は正確に、

```text
(n-1) log c ≤ log GN
log GN = log(rad GN) + GNValuationExcess
log(rad GN) ≤ σ log R + Cs
GNValuationExcess ≤ τ log R + Ce
```

であり、結論は

```text
(n-1) log c ≤ (σ+τ) log R + (Cs+Ce)
```

である。

lifted-radical growth specialization は、

```text
Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
```

であり、exceptional support の有限費用を消さず、

```text
(n-1) log c
  ≤ (σ+τ) log R + Cs + Ce + log(rad n)
```

を得る。

## 明示定数と pointwise ABC theorem

実装した定数は次である。

```lean
GNABCConstant n Cs Ce =
  max 1 (Real.exp |Cs + Ce + Real.log (rad n : ℝ)|)
```

instruction の除算型定数と同じく `T` に依存せず、依存するのは
`n`, `Cs`, `Ce` のみである。絶対値を使うことで affine constant の
符号分岐を避けた、やや粗いが明示的な定数である。

```text
one_le_GNABCConstant
Triple.abc_bound_of_liftGrowth_and_excessBudget
```

margin

```text
σ + τ ≤ (n-1) * (1+ε)
```

のもとで、

```text
c ≤ GNABCConstant n Cs Ce * rad(a*b*c)^(1+ε)
```

を証明した。証明は対数不等式を正の `(n-1)` で正規化し、
`Real.exp_le_exp`, `Real.exp_log`, `Real.exp_add`,
`Real.rpow_def_of_pos` で実数冪へ戻している。

## global final contract

次の structure を追加した。

```text
ABCGNFinalBudgetContract
```

内容は、

```text
fixed n ≥ 2
uniform lifted-radical support-growth budget
uniform exceptional valuation-excess budget
uniform non-exceptional valuation-excess budget
positive margin
```

である。

これから、

```text
abc_positive_of_GNFinalBudgetContract
```

を証明した。結論は正の ABC triple 全体に一つの `K ≥ 1` が使える
global ABC theorem である。

`a=0` / `b=0` endpoint を現行 `abc_main_axiom` と同じ生引数 surface
へ接続する拡張は行っていない。今回証明した契約と theorem の範囲は
明示的に positive triple である。`abc_main_axiom` は変更も利用もして
いない。

## 残る数学

Lean で証明済み：

```text
support budget + valuation-excess budget
  -> explicit K_epsilon ABC bound
```

未証明：

```text
uniform lifted-radical support growth
uniform exceptional valuation excess
uniform non-exceptional valuation excess
```

したがって、これは ABC 予想そのものの証明ではない。ただし
`abc_main_axiom` の positive-triple 内容を置換するために必要な一様契約は、
上記三予算へ正確に還元された。

## ローカル検証と変更範囲

```text
lake build DkMath.ABC.GNFinalBudgetBridge
Build completed successfully (8343 jobs).
```

新しい `axiom`, `sorry`, `native_decide` は追加していない。
代表的な五つの新規 endpoint に対する `#print axioms` は、
`propext`, `Classical.choice`, `Quot.sound` のみを報告した。
共有 aggregator、FLT7 module、FLT7 documentation は変更していない。
commit、push、PR、CI 操作は行っていない。
