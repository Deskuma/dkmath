# ABC–GN M1 Final Report

Date: 2026-07-26  
Status: **M1 complete — odd-prime exceptional valuation excess defeated**

## 1. 最終数学結果

任意の ABC triple `T` と奇素数 `p` について:

```lean
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
```

が次を与える。

$$
GNExceptionalValuationExcess\ p\ T.a\ T.b=0.
$$

さらに:

```lean
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

により:

```text
τe = 0
De = 0
```

が exact に供給される。positivity 仮定は不要である。

## 2. 完成 theorem chain

```text
GN_eq_geom_sum₂
  -> prime_dvd_boundary_of_dvd_GN_prime
  -> padicValNat_GN_prime_eq_one_of_dvd
  -> factorization_GN_prime_eq_one_of_dvd
  -> Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
  -> Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
  -> Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
```

数学的には:

```text
q in exceptional support
  -> q.Prime and q ∣ p
  -> q = p
  -> p ∣ GN
  -> p-adic valuation of GN = 1
  -> exceptional multiplicity excess = 0
```

である。

## 3. Fixed-five certificate との共存

固定指数 5 の theorem:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

は維持した。

```text
fixed five:
  explicit modulo 5 / modulo 25 certificate

general odd prime:
  geometric quotient / emultiplicity certificate
```

という独立した二経路であり、固定五は有用な regression certificate である。

## 4. Module / dependency surface

```text
DkMath.NumberTheory.WeightedGNBridge
  -> DkMath.ABC.GNOddPrimeExceptionalExcess
  -> DkMath.ABC.GNExceptionalExcessOddPrime

DkMath.ABC.GNFinalBudgetBridge
  -> DkMath.ABC.GNExceptionalExcessOddPrime

DkMath.ABC
  -> DkMath.ABC.GNExceptionalExcessOddPrime
```

production dependency に `DkMath.FLT.Five.*` や FLT7 WIP はない。

`GN_eq_geom_sum₂` と `prime_dvd_boundary_of_dvd_GN_prime` は neutral 化可能
だが、現状でも依存方向は正しく、直近の再利用 caller は M1 内だけである。
移動は churn と import 変更を発生させるため、M1-006 では現在位置を維持
した。将来、ABC 外の複数 caller が現れた時点で neutral owner を再評価する。

## 5. Public integration

公開入口:

```lean
import DkMath.ABC
```

から一般 odd-prime endpoint を利用できるよう、
`DkMath/ABC.lean` に:

```lean
import DkMath.ABC.GNExceptionalExcessOddPrime
```

を追加した。

## 6. Contract reduction

従来の full valuation split:

```text
exceptional coefficient/constant + non-exceptional coefficient/constant
```

は奇素数指数で:

```text
0 + non-exceptional coefficient/constant
```

へ縮退する。

caller-facing theorem により、次だけを供給すればよい。

```lean
GNNonExceptionalExcessBudgetAffine T p τn Dn
```

すると損失なく:

```lean
GNValuationExcessBudgetAffine T p τn Dn
```

を得る。

## 7. Trust audit

実行した regression build:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
  DkMath.ABC.GNExceptionalExcessFive
  DkMath.ABC.GNExceptionalExcessOddPrime
  DkMath.ABC.GNFinalBudgetBridge
  DkMath.ABC

Build completed successfully (8377 jobs).

lake build DkMath
Build completed successfully (8746 jobs).
```

代表 endpoint 3 本の axiom audit では、Lean / Mathlib の標準依存:

```text
propext
Classical.choice
Quot.sound
```

のみを許容する。新規 project axiom、`sorry`、`native_decide`、有限列挙に
よる一般証明はない。

## 8. M1 closure

```text
M1 exceptional valuation excess       defeated
M2 lifted-radical support growth       remains
M3 non-exceptional valuation excess    remains
```

M1 は閉じた Core とする。再度開く条件は、後続 integration で具体的な
counterexample、型不整合、依存欠陥が発見された場合に限る。

M2/M3 の実装は branch hygiene を守り、専用 campaign branch で開始する。
