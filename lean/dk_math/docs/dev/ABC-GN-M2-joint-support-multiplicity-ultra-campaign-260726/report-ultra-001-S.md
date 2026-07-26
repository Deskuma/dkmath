# Ultra-001S Report — summable finite Euler envelope

Date: 2026-07-27

## 判定

R の有限 Euler product を一様定数へ落とすための
finite-to-infinite majorant API を実装した。`q^(-3/2)` envelope の総和可能性と、
局所 tail estimate を一個与えれば `Q,X` 非依存定数および moment endpoint が
得られることは Lean theorem になった。

ただし、固定 `t = 1/2` における local geometric tail estimate 自体は未証明で
ある。従って S の一様定数は現時点では条件付き endpoint であり、checkpoint
全体を complete とは判定しない。

```text
local positive-excess tail                      complete
abstract summable-envelope theorem              complete
q^(-3/2) envelope summability                    complete
conditional t = 1/2 Euler constant              complete
conditional small-moment endpoint               complete
concrete t = 1/2 local geometric estimate        open
unconditional finite Euler majorant              open
```

実装は `DkMath.ABC.GNExcessEulerMajorant` に置いた。

## 1. Abstract envelope

```lean
def GNExcessLocalDensityTail
def GNExcessEulerEnvelope
theorem GNExcessLocalDensityFactor_eq_one_add_tail
theorem GNExcessLocalDensityFactor_le_exp_of_tail_le
theorem GNExcessFiniteEulerDensity_le_envelope
theorem GNExcessFiniteEulerDensity_le_envelope_of_tail
```

非負かつ summable な `g : ℕ → ℝ` が各 capped local tail を一様に支配すれば、

```text
GNExcessFiniteEulerDensity Q p b X t
  ≤ exp (∑' q, g q)
```

を得る。右辺は `Q`, `b`, `X` に依存しない。証明は R の exact finite-product
factorization、`1+x ≤ exp x`、有限和から `tsum` への単調性だけを使う。

## 2. Half-power candidate

```lean
def GNExcessHalfPowerEnvelope
def GNExcessHalfEulerConstant
theorem summable_GNExcessHalfPowerEnvelope
theorem GNExcessFiniteEulerDensity_half_le
theorem exp_GNExcessMassAt_sum_le_halfEuler_add_large
```

候補 envelope を

```text
g_p(q) = 4 * (p - 1) / q^(3/2)
```

と固定した。Mathlib の real `p`-series theorem により `g_p` の総和可能性は
無条件に証明済みである。

## 3. 最小の未証明補題

残る局所 obligation は次の一点である。

```lean
theorem GNExcessLocalDensityTail_half_le
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2)
      ≤ GNExcessHalfPowerEnvelope p q
```

数学的には、

```text
∑ j = 1 .. K-1,
  (p - 1) * exp((j/2) * log q) / q^(j+1)
  ≤ 4 * (p - 1) / q^(3/2)
```

という有限幾何級数評価である。`q` が素数なら `q ≥ 2` なので、公比
`q^(-1/2) ≤ 3/4` を使う方針が候補である。今回の実装はこの補題を仮定として
明示し、それより後の Euler product と moment composition をすべて閉じた。

## 4. 正確な停止境界

small side の analytic architecture は一個の局所補題まで圧縮された。一方、
large profile の `GNExcessLargeBoundaryProfileSum` は別戦線であり、R の
support + excess diagnosis を使う joint compensation が必要である。

従って M3-heavy summability、large-boundary absorption、uniform joint
contract、`abc_main_axiom` replacement は未証明のままである。ABC 予想の
無条件証明を主張しない。

## Local verification

```text
lake build DkMath.ABC.GNExcessEulerMajorant    success (8369 jobs)
lake build DkMath.ABC                           success (8389 jobs)
lake build DkMath                               success (8756 jobs)
representative axiom audit                      propext / Classical.choice / Quot.sound only
new production code                            no sorry / axiom / native_decide
git diff --check                               clean
```

full build に表示される既存 research module の `sorry` warning は今回の
変更によるものではない。

push、PR 更新、CI 起動・確認は行っていない。
