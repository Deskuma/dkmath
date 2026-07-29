# Ultra-001L Report — average GN valuation / finite-family depth mass

Date: 2026-07-26

## 判定

固定非例外素数 `q` に対する平均 GN valuation bound、および任意有限素数族
に対する log-weighted depth-mass bound を production Lean で証明した。

```text
single q,k counting                 inherited from Ultra-001K
finite natural layer-cake           complete
intrinsic GN depth cutoff           complete
fixed-q average valuation           complete
finite-family weighted depth mass   complete
average-to-pointwise compensation   open
```

単一 `q,k` の residue counting は再証明していない。Ultra-001K の
`card_gn_deep_lift_residue_classes_le_of_simpleRoot` を実際に全深度で合成した。

## 1. 有限 natural layer-cake

一般の有限集合 `s` と bounded natural-valued function `V` に対して、

```lean
theorem sum_nat_eq_sum_card_ge
```

を追加した。`V a ≤ K` が `a ∈ s` 上で成り立つなら、

```text
∑ a ∈ s, V a
  =
∑ k ∈ Icc 1 K, card {a ∈ s | k ≤ V a}.
```

これは exponential moment 用の旧 `exp_layer_cake` とは別に、平均 valuation
に必要な exact natural layer-cake を与える。

## 2. cutoff の構成

区間 `a ∈ [0,X]` 上で、

```lean
theorem GN_le_mul_interval_add_pow
```

により

```text
GN p a b ≤ p * (X + b)^p
```

を証明した。また、

```lean
theorem GN_ne_zero_of_prime_of_right_ne_zero
```

により、`p` が素数かつ `b ≠ 0` なら GN がゼロでないことを供給する。
したがって全 valuation depth は明示的な

```text
K := Nat.log q (p * (X + b)^p)
```

以下である。cutoff を根拠なく `X+1` と置く必要はない。

## 3. layer-explicit fixed-q bound

```lean
theorem sum_padicValNat_GN_le_of_simpleRoot_layers
```

は、`p,q` が素数、`q ∤ p`、`q ∤ b` のとき、

```text
∑ a ∈ Icc 0 X, padicValNat q (GN p a b)
  ≤
(p - 1) *
  ∑ k ∈ Icc 1 K, ((X + 1) / q^k + 1)
```

を証明する。各 layer では Ultra-001K の canonical Hensel residue count を
そのまま使用している。

## 4. 明示的 fixed-q average bound

```lean
theorem sum_div_prime_pow_Icc_le
```

で、素数 `q` に対する有限商和

```text
∑ k ∈ Icc 1 K, N / q^k ≤ N
```

を Legendre の factorial valuation formula から得た。これにより、

```lean
theorem sum_padicValNat_GN_le_of_simpleRoot
```

は次の完全に明示的な評価を与える。

```text
∑ a ∈ Icc 0 X, padicValNat q (GN p a b)
  ≤
(p - 1) * ((X + 1) + Nat.log q (p * (X + b)^p)).
```

これは NOTE-ultra-001-K が要求した固定 `p,q,b,X` の平均 valuation theorem
そのものである。

## 5. weighted / finite-family 版

固定 `q` について、

```lean
theorem sum_padicValNat_GN_mul_log_le_of_simpleRoot
```

が上の bound に `Real.log q` を掛けた評価を与える。さらに、

```lean
theorem sum_GN_depthMass_over_interval_le
```

は、任意の有限素数族 `Q` が各 `q ∈ Q` について
`q ∤ p`、`q ∤ b` を満たすとき、

```text
∑ a ∈ Icc 0 X, ∑ q ∈ Q, v_q(GN p a b) * log q
  ≤
∑ q ∈ Q,
  (p - 1) * (X + 1 + log_q (p * (X+b)^p)) * log q
```

を証明する。これは finite-family averaged GN depth mass の直接 API である。

## 6. 証明境界

本 checkpoint は平均評価を閉じたが、次はまだ証明していない。

- triple ごとに有効な有限素数族 `Q` の選択
- 平均 bound から個々の triple に戻る deterministic compensation
- `ABCGNOddPrimeJointContract`
- `abc_main_axiom` の置換

従って、これは ABC 予想の完全証明ではない。新しい frontier は、
average-to-pointwise の補償原理である。

## 7. Local verification

```text
lake build DkMath.ABC.GNLegacyTailCountingBridge   success (8361 jobs)
lake build DkMath.ABC                              success (8381 jobs)
lake build DkMath                                  success (8751 jobs)
new theorem axiom audit                            propext / Classical.choice / Quot.sound only
new production code                               no sorry / axiom / native_decide
git diff --check                                  clean
```

push、PR 更新、CI 起動・確認は行っていない。
