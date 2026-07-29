# Ultra-001I Report — 旧 ABC 塔の再接続

Date: 2026-07-26  
Status: **legacy tail/counting bridge complete / Hensel cover construction open**

## 調査対象

`MEMO-ultra-001.md` が指摘した旧戦線:

```text
SquareTailBasic.twoTail / piSqRad
CountPowersDividing2n1
FiniteChernoffBasic.exp_layer_cake
PadicTelescoping 系の residue counting
```

を現行の:

```text
GNNonExceptionalSupportProduct
GNNonExceptionalValuationExcess
GNNonExceptionalDepthMass
```

へ接続した。

## Production module

```text
DkMath.ABC.GNLegacyTailCountingBridge
```

## Tail bridge

完全な non-exceptional prime-power 部分を整数として再構成する:

```lean
GNNonExceptionalPart p a b
```

を追加した。factorization は exact に:

```text
q ∈ GNNonExceptionalSupport
  -> v_q(GNNonExceptionalPart) = v_q(GN)

q ∉ GNNonExceptionalSupport
  -> v_q(GNNonExceptionalPart) = 0
```

となる。従って:

```lean
rad_GNNonExceptionalPart_eq_supportProduct
valuationExcess_GNNonExceptionalPart_eq
```

が成立し、旧 ABC 塔の decomposition を直接再利用して:

```lean
GNNonExceptionalValuationExcess_eq_log_sqTail

GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail
```

を得た。すなわち現在の excess は exact に:

```text
log piSqRad(non-exceptional part)
+
log twoTail(non-exceptional part)
```

である。

## Counting bridge

Hensel/cyclotomic 側が有限な residue address set `R` を返すための中立契約:

```lean
GNDeepLiftResidueCover p q b k R
```

を追加した。これから旧 residue counting を再利用して:

```lean
card_gn_deep_lift_residue_classes_le
```

を証明した。`R.card ≤ p - 1` なら:

```text
#{a ∈ [0,X] | q^k ∣ GN p a b}
  ≤ (p - 1) * ((X + 1) / q^k + 1)
```

を得る。

さらに:

```lean
gn_deep_lift_filter_eq_padic_depth_filter
exp_gn_padic_layer_cake
```

により divisibility layer を `padicValNat` layer へ変換し、旧
`exp_layer_cake` に GN depth を直接入力できる。

## Exact remaining arithmetic input

未証明なのは counting の有限集合操作ではなく:

```lean
∃ R, R.card ≤ p - 1 ∧ GNDeepLiftResidueCover p q b k R
```

という Hensel/cyclotomic residue cover の構成である。

この cover が得られても結論は平均・密度評価であり、全 Triple に対する
pointwise `ABCGNOddPrimeJointContract` とは区別する。

## Verification

```text
lake build DkMath.ABC.GNLegacyTailCountingBridge DkMath.ABC
Build completed successfully (8381 jobs).

lake build DkMath
Build completed successfully (8751 jobs).
```

代表 endpoints の axiom audit:

```text
propext
Classical.choice
Quot.sound
```

のみ。新規 `sorry`、`axiom`、`native_decide` は使用していない。
