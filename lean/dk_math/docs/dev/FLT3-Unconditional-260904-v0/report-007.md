# FLT3U-007 実装報告: Eisenstein Norm-Euclidean Foundation

## 実装範囲

instruction-007 の FLT3U-006A checkpoint を実装した。対象は具体的な
`EisensteinInt = TraceOneInt (-1)` の norm-Euclidean domain だけであり、
generic `TraceOneInt s` の Euclidean structure は追加していない。

cube extraction、unit sector、strict descent、最終 FLT3 定理はこの checkpoint
の対象外である。

## 追加 module と imports

[EisensteinEuclidean.lean](../../../DkMath/FLT/Three/EisensteinEuclidean.lean)
を追加した。実際の import は次の三つである。

```text
import DkMath.FLT.Three.EisensteinConjugateCoprime
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.EuclideanDomain
```

FLT3 Main/Basic/Core、GEisenstein bridge、FLT5、FLT7 の production module、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## Domain foundation

completed-square 型の評価

```text
norm (r,s) = r^2 + r*s + s^2
```

から

```text
eisenstein_norm_eq_zero_iff : norm x = 0 ↔ x = 0
```

を証明した。これを用いて `NoZeroDivisors`、`Nontrivial`、`IsDomain` の
具体的な `TraceOneInt (-1)` instance を構成した。

## Rational geometry and division data

`EisensteinRat = ℚ × ℚ` と

```text
eisensteinRatNorm (u,v) = u^2 + u*v + v^2
```

を導入し、次の completed square を kernel-checked にした。

```text
N_Q(u,v) = (u + v/2)^2 + (3/4)*v^2
```

`|v| ≤ 1/2` と `|u+v/2| ≤ 1/2` から exact に `N_Q ≤ 7/16 < 1`
を得た。浮動小数点近似は使っていない。

quotient numerator `x * conj y` の座標は、s = -1 の係数として

```text
fst = x.fst * (y.fst + y.snd) + x.snd * y.snd
snd = x.snd * y.fst - x.fst * y.snd
```

を独立に証明した。

quotient は

```text
n = round B
m = round (A + (B - n)/2)
q = m + n*tau
```

とする skew rounding で定義した。`abs_sub_round` から second-coordinate
誤差と skew first-coordinate 誤差がともに `≤ 1/2` になることを証明した。

## Remainder and Euclidean size

`eisensteinRemainder x y = x - eisensteinQuotient x y * y` とし、再構成式、
zero divisor における quotient-zero を証明した。さらに `y ≠ 0` のもとで、

```text
N(r) = N(y) * N_Q(A-m, B-n)
```

の rational remainder norm identity を証明した。

Euclidean size は

```text
eisensteinEuclideanSize x = Int.natAbs (norm x)
```

とし、非零元での正性、積に対する乗法性、norm 非負性を証明した。7/16 bound
と `N(y) > 0` から

```text
eisensteinEuclideanSize (eisensteinRemainder x y)
  < eisensteinEuclideanSize y
```

を得た。

## EuclideanDomain instance

次の concrete instance を追加した。

```text
traceOneNegOneEuclideanDomain :
  EuclideanDomain (TraceOneInt (-1))
```

GCDMonoid instance は追加していない。preferred ownership に従い、次の
FLT3U-006B に残している。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.EisensteinEuclidean
```

focused build は `Build completed successfully (8716 jobs).` で終了した。
新規 module 自身の warning はない。一方、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning
は継続している。

`eisenstein_norm_eq_zero_iff`、covering bound、`eisenstein_remainder_size_lt`、
`traceOneNegOneEuclideanDomain` の `#print axioms` は
`propext`、`Classical.choice`、`Quot.sound` のみであり、`sorryAx` や
project-specific axiom はない。source の forbidden import、`sorry`、`axiom`、
完結済み FLT3 shortcut も監査済みである。

## Outcome

Outcome A。norm に基づく strict remainder bound とともに、
`EuclideanDomain (EisensteinInt)` を kernel-checked に提供した。

FLT3U-006B に残る gate は、この Euclidean/GCD infrastructure と 006 の
`beta`・`conj beta` relative-prime certificate、`norm beta = B^3` を使った
unit-times-cube extraction

```text
beta = epsilon * gamma^3
```

である。この checkpoint では実装していない。
