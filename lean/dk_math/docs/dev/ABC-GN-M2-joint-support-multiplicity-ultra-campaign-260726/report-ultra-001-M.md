# Ultra-001M Report — q-sensitive average valuation excess

Date: 2026-07-26

## 判定

`q` 感度を保持した full valuation bound と、第2層以降だけを数える
valuation-excess bound を production Lean で証明した。

```text
q-sensitive quotient sum                  complete
depth-two excess layer-cake                complete
fixed-q average excess                     complete
finite-family weighted excess              complete
canonical interval non-exceptional family  complete
boundary-address compensation              open
```

実装は `DkMath.ABC.GNAverageExcess` に分離した。

## 1. q-sensitive geometric bounds

```lean
theorem sum_div_prime_pow_Icc_le_div_pred
```

は素数 `q` に対し、

```text
∑ k ∈ Icc 1 K, N / q^k ≤ N / (q - 1)
```

を証明する。さらに excess 用の、

```lean
theorem sum_div_prime_pow_Icc_two_le
```

は、

```text
∑ k ∈ Icc 2 K, N / q^k ≤ N / (q * (q - 1))
```

を与える。後者が M3 の密度項に必要な `q^-2` decay である。

## 2. depth-two natural layer-cake

```lean
theorem sum_nat_pred_eq_sum_card_ge_two
```

により、`V a ≤ K` のとき、

```text
∑ a ∈ s, (V a - 1)
  =
∑ k ∈ Icc 2 K, card {a ∈ s | k ≤ V a}
```

を exact に証明した。第1層は完全に除かれている。

## 3. fixed-q average excess

```lean
theorem sum_padicValNat_pred_GN_le_of_simpleRoot
```

は `p,q` が素数、`q ∤ p`、`q ∤ b` のとき、

```text
∑ a ∈ Icc 0 X, (padicValNat q (GN p a b) - 1)
  ≤
(p - 1) *
  ((X + 1) / (q * (q - 1))
    + (Nat.log q (p * (X + b)^p) - 1)).
```

右辺の第一項は density、第二項は各深度に残る一個の boundary address
である。full valuation についても、

```lean
theorem sum_padicValNat_GN_le_of_simpleRoot_div_pred
```

で密度項を `(X+1)/(q-1)` まで改善した。

## 4. finite-family / canonical family

```lean
noncomputable def GNExcessMassAt
theorem sum_GNExcessMassAt_over_interval_le
```

により任意有限素数族の log-weighted excess average を証明した。

さらに、

```lean
noncomputable def GNNonExceptionalIntervalPrimeFamily
theorem sum_GNNonExceptionalIntervalExcessMass_le
```

を追加した。この canonical family は区間中の全 GN non-exceptional support
を合併し、固定 boundary `b` を割る素数だけを除く。従って family 内では、

```text
q prime
q ∤ p
q ∤ b
```

が定義から自動的に得られる。

## 5. 境界

密度由来の各 summand は `log q / (q(q-1))` 型まで圧縮された。ただし、
全素数上の無限級数を一個の普遍実定数で抑える解析定理は本 checkpoint
では証明していない。また各深度の boundary-address 項も残る。

従って M3 の平均密度部分は最終形に近づいたが、pointwise M3 budget や
`ABCGNOddPrimeJointContract` はまだ得ていない。

## Local verification

```text
lake build DkMath.ABC.GNAverageExcess   success (8362 jobs)
representative axiom audit              propext / Classical.choice / Quot.sound only
new production code                    no sorry / axiom / native_decide
```

push、PR 更新、CI 起動・確認は行っていない。
