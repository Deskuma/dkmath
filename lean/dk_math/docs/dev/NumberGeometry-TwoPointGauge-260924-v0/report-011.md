# NumberGeometry-TwoPointGauge NGEO-011 実装報告

## 1. 結果

Outcome A。FLT や p=7 固有理論から独立した、一般の正整数 `p` に対する
signed `2 * p` phase layer を実装した。

primitive `2 * p` phase `eta` から、full turn、half turn、even/odd phase の
`p`-th power split、`eta^2` による p-phase generator、signed polynomial
equations を提供している。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/Phase/TwoPrime.lean`
- `DkMathTest/NumberGeometry/TwoPrimePhaseAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-011.md`

変更:

- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Phase.TwoPrime` を public facade へ追加。

Production phase module は Mathlib の roots-of-unity API だけに依存し、
`DkMath.FLT.*`、`DkMath.FLT.Seven.*`、LogGauge、PrimeScale、UnitCycle は
import していない。

## 3. IsPrimitiveRoot half-turn audit

Mathlib には次の短い ownership route がある。

```text
IsPrimitiveRoot.pow
IsPrimitiveRoot.eq_neg_one_of_two_right
```

`IsPrimitiveRoot eta (2 * p)` と `0 < p` から、`IsPrimitiveRoot (eta ^ p) 2`
を `IsPrimitiveRoot.pow` で得られる。さらに `NoZeroDivisors` の下で
`eq_neg_one_of_two_right` がこの primitive second root を `-1` と同定する。

そのため half-turn は手作業の roots-of-unity theory ではなく、Mathlib の
既存 ownership を使う `TwoPrimePhase.halfTurn` として実装した。

## 4. TwoPrimePhase representation

最終 packet は次の形である。

```lean
structure TwoPrimePhase (R : Type*) [CommRing R] [NoZeroDivisors R] (p : ℕ) where
  eta : R
  positive : 0 < p
  primitive : IsPrimitiveRoot eta (2 * p)
```

`eta ^ (2 * p) = 1` と `eta ^ p = -1` は保存フィールドに重複して持たせず、
それぞれ primitive ownership から theorem として導出している。

## 5. Full-turn / half-turn ownership

```lean
TwoPrimePhase.fullTurn
TwoPrimePhase.halfTurn
```

`fullTurn` は `P.primitive.pow_eq_one` の直接 wrapper であり、
`halfTurn` は上記 Mathlib half-turn route の wrapper である。

## 6. Even / odd phase definitions

次を定義した。

```lean
TwoPrimePhase.evenPhase P j := P.eta ^ (2 * j)
TwoPrimePhase.oddPhase  P j := P.eta ^ (2 * j + 1)
```

それぞれについて次を証明した。

```lean
TwoPrimePhase.evenPhase_pow
TwoPrimePhase.oddPhase_pow
```

内容は `evenPhase j ^ p = 1` と `oddPhase j ^ p = -1` であり、座標展開や
三角関数は使用していない。

## 7. zeta = eta^2 API

```lean
TwoPrimePhase.zeta
TwoPrimePhase.zeta_pow_p
TwoPrimePhase.evenPhase_eq_zeta_pow
TwoPrimePhase.oddPhase_eq_eta_mul_zeta_pow
```

`zeta_pow_p` は `P.fullTurn` から導出した。`zeta_isPrimitiveRoot` も
`IsPrimitiveRoot.pow` により実装し、`Nat.Prime p` を受ける API として公開した。
実際の proof route は `p > 0` だけを使い、prime 固有の追加理論は導入していない。

## 8. Finite p+p sectors

次を `Fin p` index で定義した。

```lean
TwoPrimePhase.evenPhaseFin
TwoPrimePhase.oddPhaseFin
```

さらに次を実装した。

```lean
TwoPrimePhase.evenPhaseFin_injective
TwoPrimePhase.oddPhaseFin_injective
TwoPrimePhase.evenPhaseFin_ne_oddPhaseFin
```

primitive phase の `pow_inj` を使い、`2 * i` と `2 * j + 1` の exponent bounds
を `Fin` の範囲から処理している。従って even sector 内・odd sector 内の重複はなく、
even/odd sector は互いに disjoint である。

## 9. Signed p-th-power split

```lean
TwoPrimePhase.even_signed_equation
TwoPrimePhase.odd_signed_equation
```

任意の `Y : R` に対し、phase multiple を `X` とすると、

```text
X = evenPhase j * Y -> X^p - Y^p = 0
X = oddPhase j  * Y -> X^p + Y^p = 0
```

を `mul_pow` と even/odd の p-th-power theorem から証明した。

## 10. Exact product-factorization status

DEFERRED。`X^p - Y^p` / `X^p + Y^p` の finite product factorization は今回の
required signed root equations に不要であり、既存 API の大きな product proof を
追加していない。

## 11. Canonical complex 2p phase

次を実装した。

```lean
complexEta p := Complex.exp (2 * Real.pi * Complex.I / (2 * p))
complexEta_isPrimitiveRoot
complexTwoPrimePhase
complexEta_pow_eq_neg_one
```

`complexEta_isPrimitiveRoot` は `Complex.isPrimitiveRoot_exp` を直接利用し、
`complexEta_pow_eq_neg_one` は constructed `TwoPrimePhase` の `halfTurn` から
導出した。Complex half-turn を axiom として仮定していない。

## 12. CF2D calibration

test/audit file に次を追加した。

```lean
DkMathTest.NumberGeometry.regularKernel_twoPrime_exactOrder
```

既存 owner theorem `orderOf_regularKernel` から

```text
orderOf (regularKernel (2 * p)) = 2 * p
```

を確認している。

CF2D exact 2p order: LEAN-CONFIRMED。

CF2D regular kernel と canonical complex `eta` の identification は
DEFERRED。CycleDivision の theorem ownership は複製していない。

## 13. 意図的に主張していないこと

- `X^p - Y^p = 0` の全解が even phase であるという converse。
- `X^p + Y^p = 0` の全解が odd phase であるという converse。
- signed phase split による FLT の証明。
- `p = 7` への限定。
- CF2D regular kernel と Complex primitive root の definitional equality。
- exact cyclotomic product factorization。
- seventh-cyclotomic carrier や FLT7 との接続。

## 14. 検証

成功した build:

```text
lake build DkMath.NumberGeometry.Phase.TwoPrime
Build completed successfully (3092 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (8940 jobs)

lake build DkMathTest.NumberGeometry.TwoPrimePhaseAxiomAudit
Build completed successfully (8979 jobs)
```

Audit の substantive declarations は、`propext`、`Classical.choice`、
`Quot.sound` など既存 logical infrastructure のみを使用している。
新しい `axiom`、`sorryAx`、`unsafe`、`sorry`、`admit` は追加していない。

## 15. NGEO-012 proposed scope

NGEO-012 では `p = 7` を具体化し、今回の general `TwoPrimePhase` と既存の
seventh-cyclotomic code / CF2D fourteen-phase calibration の接続を監査する。
対象は bounded な phase identification・order・signed sector calibration に限定し、
FLT の証明、prime distribution、未証明の global phase dynamics は含めない。

NGEO-011 はここで終了する。
