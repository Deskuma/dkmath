# M1-003 Report: 指数 5 の exceptional excess 完全消去

Date: 2026-07-26  
Outcome: **完了 — exceptional finite sum と affine budget をともに厳密な 0 へ閉じた**

## 1. 実装ファイル

新規モジュール:

```text
DkMath/ABC/GNExceptionalExcessFive.lean
```

import:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

M1-002 の低依存な局所算術 kernel は変更せず、新規ファイルを
finite-sum / final-budget 接続層とした。FLT5 import と集約モジュール変更は
ない。

## 2. 完成した endpoint

### Exceptional finite sum

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0
```

### Exact zero affine budget

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple) :
    GNExceptionalExcessBudgetAffine T 5 0 0
```

両 theorem とも `0 < T.a`、`0 < T.b` その他の positivity 仮定を必要と
しない。

## 3. Finite-sum の証明経路

`GNExceptionalValuationExcess` だけを unfold し、filtered support 上の各
`q` の summand が 0 であることを示した。

```text
q ∈ factorization.support.filter (fun q => q ∣ 5)
  -> q ∈ factorization.support
  -> q ∈ primeFactors
  -> q.Prime
  -> q ∣ 5
  -> q = 5
```

support から prime への変換には canonical API:

```lean
Nat.support_factorization
Nat.prime_of_mem_primeFactors
```

を用いた。`q = 5` には:

```lean
Nat.prime_dvd_prime_iff_eq
```

を用いたため、`q = 1` の分岐を手動で処理する必要はない。

## 4. Support から GN divisibility への接続

`q = 5` を代入した後、factorization support membership から:

```lean
Finsupp.mem_support_iff.mp hqSupport :
  (GN 5 T.a T.b).factorization 5 ≠ 0
```

を得て、canonical bridge:

```lean
Nat.dvd_of_factorization_pos
```

により:

```lean
5 ∣ GN 5 T.a T.b
```

へ接続した。

続いて M1-002 の既存 theorem:

```lean
factorization_five_GN_five_eq_one_of_dvd T.hcop h5GN
```

で multiplicity を 1 に書き換えた。その結果、

```text
((1 - 1 : ℕ) : ℝ) * Real.log (5 : ℝ) = 0
```

となり、各 summand と有限和全体が `simp` で 0 へ閉じた。modulo 5 /
modulo 25 算術は再証明していない。

## 5. Zero-budget wrapper

`GNExceptionalExcessBudgetAffine` を unfold し、finite-sum zero theorem で
左辺を書き換えた。残る目標は:

```text
0 ≤ 0 * Real.log (rad (T.a * T.b * T.c) : ℝ) + 0
```

であり、`simp` で閉じた。したがって指数 5 では exceptional budget の
係数と定数を正確に:

```text
τe = 0
De = 0
```

へ固定できる。

## 6. 検証

実行:

```text
lake build DkMath.ABC.GNExceptionalExcessFive
```

結果:

```text
Build completed successfully (8345 jobs).
```

一時 audit module から両 endpoint に `#print axioms` を実行した。
結果はいずれも:

```text
propext
Classical.choice
Quot.sound
```

のみであり、新規 project axiom はない。`sorry`、`axiom`、
`native_decide` は追加していない。

## 7. Checkpoint 境界

固定指数 5 における M1 minimum victory は達成した。

```text
GNExceptionalValuationExcess 5 T.a T.b = 0
GNExceptionalExcessBudgetAffine T 5 0 0
```

指示どおり M1-004 の一般奇素数化、M1-005、M2、M3、aggregator 変更には
進んでいない。

