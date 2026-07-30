# M1-002 Review: exponent-five exceptional valuation-one kernel

Date: 2026-07-26  
Commit: `3fa7baceb34f7b184168e68fb16b9d76bf4d122b`  
Decision: **全面採用**

## 1. Summary

M1-002 は指定された停止境界を守り、指数 5 の局所例外 channel を正確に閉じた。

主結果:

```lean
Nat.Coprime a b →
5 ∣ GN 5 a b →
padicValNat 5 (GN 5 a b) = 1
```

および factorization 版:

```lean
Nat.Coprime a b →
5 ∣ GN 5 a b →
(GN 5 a b).factorization 5 = 1
```

重大問題、主要問題、修正必須事項はない。

## 2. Mathematical review

### 2.1 Canonical GN specialization

`GN_five_eq_explicit` は FLT5 専用多項式を再利用せず、canonical `GN_eq_sum` から指数 5 の有限展開を得ている。

```text
GN 5 a b
  = a^4 + 5*a^3*b + 10*a^2*b^2 + 10*a*b^3 + 5*b^4
```

したがって ABC 側から FLT5 実装へ逆依存せず、一般 GN の specialization として所有権が正しい。

### 2.2 Divisibility routing

```text
5 ∣ GN 5 a b
  -> GN 5 a b ≡ a^4 mod 5
  -> 5 ∣ a^4
  -> 5 ∣ a
```

の経路は直接的で、余分な positivity / nonzero 仮定を必要としない。

### 2.3 No-lift modulo 25

`a = 5*k` を代入して得た

```text
GN 5 (5*k) b = 25*K + 5*b^4
```

から、仮に `25 ∣ GN` なら `5 ∣ b^4`、従って `5 ∣ b` を得る。

`hcop : Coprime (5*k) b` から `Coprime 5 b` を抽出して矛盾するため、

```text
5 ∣ GN かつ Coprime a b
  -> 25 ∤ GN
```

が閉じる。

`omega` による witness `t - K` の構成も、分解等式から `K ≤ t` と `b^4 = 5*(t-K)` を同時に回収しており、Nat subtraction の欠損はない。

### 2.4 Exact valuation

既存 API

```lean
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
```

を用いて

```text
1 ≤ v_5(GN)
¬ 2 ≤ v_5(GN)
```

を結合し、exact valuation one を得ている。

`GN 5 a b ≠ 0` は公開仮定にせず、`GN = 0 -> 25 ∣ GN` と no-lift の矛盾から内部導出している。この theorem surface は最小である。

### 2.5 Factorization bridge

```lean
Nat.factorization_def
```

により `padicValNat = 1` を factorization multiplicity one へ直接輸送している。M1-003 の summand 消去に必要な形が既に供給された。

## 3. Dependency and scope review

採用点:

```text
import DkMath.ABC.GNValuationExcess
no DkMath.FLT.Five.* import
no aggregator modification
no unrelated refactor
no sorry / axiom / native_decide
```

モジュール名は general odd-prime campaign を表す一方、現時点の内容は exponent five に限定されている。しかし module docstring がその境界を明示し、M1-004 で一般化する計画と整合するため問題ない。

## 4. Build and trust boundary

報告された focused build と axiom audit は checkpoint の要求を満たす。

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
Build completed successfully
```

公開 7 theorem に新規 project axiom はなく、標準依存のみである。

## 5. M1-003 design decision

M1-002 の局所算術ファイルは低い依存で閉じている。M1-003 では `GNFinalBudgetBridge` まで必要になるため、既存ファイルを高位 bridge へ依存させず、薄い新規接続モジュールを推奨する。

```text
DkMath/ABC/GNExceptionalExcessFive.lean
```

推奨 import:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

M1-003 の主定理は positivity を必要としない強い形を第一候補とする。

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0
```

理由:

```text
filtered support membership
  -> q ∈ factorization.support
  -> q is prime and q ∣ GN
  -> q ∣ 5
  -> q = 5
  -> factorization at 5 = 1 by T.hcop
  -> summand = 0
```

続いて exact zero budget を同じく無条件で供給する。

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple) :
    GNExceptionalExcessBudgetAffine T 5 0 0
```

## 6. Verdict

```text
M1-002 complete
minimum local kernel achieved
M1-003 may start
```

M1-002 は、指数 5 における唯一の exceptional channel が存在する場合、その multiplicity が exact one であることを Lean 上で固定した。次 checkpoint は新しい算術を必要とせず、この局所核を finite filtered sum と budget predicate へ接続するだけである。
