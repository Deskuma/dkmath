# M1-005 Report: 一般奇素数 exceptional excess と zero budget

Date: 2026-07-26  
Outcome: **完了 — 一般奇素数の exceptional finite sum を完全消去**

## 1. 実装

新規 module:

```text
DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

imports:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

局所 arithmetic kernel と finite-sum / budget bridge の分離を維持した。

## 2. 完成 endpoint

```lean
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0

theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

positivity 仮定は不要だった。

## 3. Exceptional support の消去

filtered support の各 `q` について:

```text
q ∈ factorization.support
  -> q ∈ primeFactors
  -> q.Prime

q.Prime + q ∣ p + p.Prime
  -> q = p
```

使用 API:

```lean
Nat.support_factorization
Nat.prime_of_mem_primeFactors
Nat.prime_dvd_prime_iff_eq
```

`q = p` の代入後、support membership を:

```lean
Finsupp.mem_support_iff
Nat.dvd_of_factorization_pos
```

で `p ∣ GN p T.a T.b` へ変換した。

M1-004 endpoint:

```lean
factorization_GN_prime_eq_one_of_dvd hp hpOdd T.hcop hpGN
```

を代入すると multiplicity factor は `1 - 1 = 0` となり、全 summand と
finite sum が 0 へ閉じた。

## 4. Contract simplification

exact zero theorem により:

```text
τe = 0
De = 0
```

を供給した。

さらに production-facing wrapper:

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (T : Triple) {p : ℕ} {τn Dn : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

を追加した。これは:

```lean
GNValuationExcessBudgetAffine.of_split
```

へ zero exceptional budget と `hn` を渡す薄い wrapper であり、final bridge
proof を重複していない。

したがって odd-prime exponent では full valuation budget の係数・定数は
非例外側と完全に一致する。

## 5. 検証

focused build:

```text
lake build DkMath.ABC.GNExceptionalExcessOddPrime
Build completed successfully (8349 jobs).
```

M1-006 の統合検証・公理監査結果は `FINAL_REPORT.md` に記録する。

