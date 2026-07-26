# Ultra-001S2 Report — unconditional half-power Euler majorant

Date: 2026-07-27

## 判定

Ultra-001S に残っていた唯一の局所解析補題を証明し、有限 small-profile
Euler density と moment endpoint から `htail` 仮定を除去した。

```text
half-log square identity                       complete
prime half-power ratio ≤ 3/4                   complete
local-weight geometric decay                   complete
finite geometric tail ≤ 4                      complete
q^(-3/2) local tail envelope                    complete
unconditional half-Euler density endpoint      complete
unconditional small-profile moment endpoint    complete
U-001S                                          complete
```

実装は `DkMath.ABC.GNExcessEulerMajorant` に置いた。

## 1. 局所幾何級数

公開 endpoint は次である。

```lean
theorem GNExcessLocalDensityTail_half_le
    {p q K : ℕ}
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
      GNExcessHalfPowerEnvelope p q
```

`x = exp ((1/2) * log q)` と置き、まず `x^2 = q` を示した。素数性から
`q ≥ 2` を使うと、

```text
x / q ≤ 3 / 4
```

となる。これを局所 weight の exact recurrence に代入し、

```text
weight (j + 1) ≤ (3 / 4) * weight j
```

を得た。induction により各項を `weight 1 * (3/4)^j` で抑え、専用の有限
幾何級数恒等式

```text
sum (3/4)^i = 4 * (1 - (3/4)^n) ≤ 4
```

と合成した。

最後に positive-base `Real.rpow_def_of_pos` を使い、

```text
4 * weight 1 = 4 * (p - 1) / q^(3/2)
```

を確認した。右辺は `GNExcessHalfPowerEnvelope p q` そのものである。

## 2. 無条件 endpoint

```lean
theorem GNExcessFiniteEulerDensity_half_le
theorem exp_GNExcessMassAt_sum_le_halfEuler_add_large
```

両 theorem から外部 `htail` 引数を削除した。従って有限素数族 `Q` が素数族
である限り、small profile の Euler density は

```text
GNExcessHalfEulerConstant p
```

で無条件に抑えられる。この定数は `Q`, `b`, `X` に依存しない。

moment endpoint は、

```text
∑ a ∈ Icc 0 X, exp ((1/2) * GNExcessMassAt Q p b a)
  ≤ 2 * (X + 1) * GNExcessHalfEulerConstant p
      + GNExcessLargeBoundaryProfileSum Q p b X (1/2)
```

である。

## 3. 正確な停止境界

S の small-profile analytic side は閉じた。ただし large profile の
`GNExcessLargeBoundaryProfileSum` は明示的に残っている。従って今回の結果は
large-boundary absorption、M3-heavy summability、uniform joint contract、
`abc_main_axiom` replacement を証明しない。ABC 予想の無条件証明を主張しない。

次の自然な checkpoint は、large exact profile を区間長より大きい非例外
squareful divisor packet へ変換する U-001T である。

## Local verification

```text
lake build DkMath.ABC.GNExcessEulerMajorant    success (8369 jobs)
lake build DkMath.ABC                           success (8389 jobs)
lake build DkMath                               success (8756 jobs)
representative axiom audit                      propext / Classical.choice / Quot.sound only
new production code                            no sorry / axiom / native_decide
git diff --check                               clean
```

full build に表示される既存 research module の `sorry` warning は今回の変更に
よるものではない。

push、PR 更新、CI 起動・確認は行っていない。
