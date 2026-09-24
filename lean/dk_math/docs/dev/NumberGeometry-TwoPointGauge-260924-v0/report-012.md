# NumberGeometry-TwoPointGauge NGEO-012 実装報告

## 1. 結果

Outcome A。一般の signed `2 * p` phase layer を `p = 7` に特殊化し、既存の
degree-six cyclotomic carrier と CF2D fourteen-cycle を bounded に校正した。

この checkpoint で実装したのは phase、sector、order、carrier identification
であり、FLT の証明や p=7 固有の未実装理論ではない。

## 2. 変更ファイル

追加:

- `DkMath/NumberGeometry/Phase/SevenTreasure.lean`
- `DkMath/FLT/Seven/NumberGeometryFourteenPhaseBridge.lean`
- `DkMathTest/NumberGeometry/SevenTreasureAxiomAudit.lean`
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-012.md`

変更:

- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.Phase.SevenTreasure` を public facade へ追加。

`SevenTreasure.lean` は `DkMath.FLT.*` を import せず、FLT/Seven bridge は
別モジュールとして一方向に保持した。`DkMath.FLT.Seven.lean` への追加は行って
いない。

## 3. FourteenPhase

次を実装した。

```lean
abbrev FourteenPhase (R) [CommRing R] [NoZeroDivisors R] := TwoPrimePhase R 7
complexFourteenPhase : FourteenPhase ℂ
```

canonical complex witness は既存の `complexTwoPrimePhase 7` を再利用している。

## 4. 7+7 sector

`evenSector` と `oddSector` を `Fin 7` の image として定義し、次を確認した。

- `evenSector_card`: `7`
- `oddSector_card`: `7`
- `evenSector_disjoint_oddSector`
- `sector_card`: `14`

sector の card は even/odd の injectivity と disjoint union から導出している。

## 5. Signed seventh equations

次の thin wrappers を公開した。

```lean
FourteenPhase.even_seventh_equation
FourteenPhase.odd_seventh_equation
```

前者は phase multiple の seventh-power difference equation、後者は seventh-power
sum equation である。

## 6. Complex witness

`complexFourteenPhase_fullTurn` と `complexFourteenPhase_halfTurn` により、
canonical complex phase の `eta^14 = 1` と `eta^7 = -1` を確認した。

## 7. CF2D order fourteen

audit file に次を追加した。

```lean
regularKernel_fourteen_exactOrder
regularKernel_fourteen_pow_eq_one
```

既存 owner theorem `orderOf_regularKernel` と `regularKernel_pow_eq_one` から
`regularKernel 14` の exact order fourteen と fourteen-cycle completion を確認した。

Status: LEAN-CONFIRMED。

## 8. 既存 facts の再利用

FLT/Seven bridge は既存の次の facts を再証明せずに再利用した。

- `SevenCyclotomicDegreeSixInt.zeta_pow_seven`
- `SevenCyclotomicDegreeSixInt.zeta_ne_one`
- `SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot`
- `SevenCyclotomicDegreeSixInt.ringIsDomain`

## 9. eta14 definition

既存 carrier の `zeta` に対して、次を定義した。

```lean
eta14 : Ring := -(zeta ^ 4)
```

これは `eta14^2 = zeta` を満たす十四位相の carrier-side generator である。

## 10. Square / seventh / fourteenth identities

次を Lean theorem として実装した。

- `eta14_sq : eta14 ^ 2 = zeta`
- `eta14_pow_seven : eta14 ^ 7 = -1`
- `eta14_pow_fourteen : eta14 ^ 14 = 1`

## 11. Primitive order status

`eta14_isPrimitiveRoot : IsPrimitiveRoot eta14 14` を実装した。

Status: LEAN-CONFIRMED。

証明では `eta14^2 = zeta` と既存の primitive seventh root を使い、指数の範囲
`0 < l < 14` に対して `l = 7` を排除している。

## 12. Packet status

次の carrier packet を構成した。

```lean
degreeSixFourteenPhase : FourteenPhase Ring
```

さらに `degreeSixFourteenPhase_zeta` と `degreeSixFourteenPhase_evenPhase_one`
により、generic packet の squared generator と first even phase を既存の `zeta`
へ同定した。

Status: LEAN-CONFIRMED。

## 13. zeta identification

`degreeSixFourteenPhase_zeta` は generic `zeta = eta^2` と existing carrier
`zeta` の equality を明示する。`degreeSixFourteenPhase_evenPhase_one` は
`evenPhase 1 = zeta` を thin interpretation として提供する。

## 14. No FLT7 theorem

この checkpoint では FLT7 theorem、Fermat equation の global contradiction、
prime existence、real-sector elimination、away-branch discharge は追加していない。
既存 carrier theorem の修正・再証明も行っていない。

## 15. Status table

| Item | Status |
| --- | --- |
| Pure `FourteenPhase` specialization | LEAN-CONFIRMED |
| Complex full/half turn | LEAN-CONFIRMED |
| 7+7 cards and disjointness | LEAN-CONFIRMED |
| Signed seventh equations | LEAN-CONFIRMED |
| CF2D order fourteen | LEAN-CONFIRMED |
| `eta14` square/seventh/fourteenth identities | LEAN-CONFIRMED |
| `eta14` primitive order fourteen | LEAN-CONFIRMED |
| Existing degree-six carrier packet | LEAN-CONFIRMED |
| Phase-to-carrier interpretation beyond the thin equalities | STRUCTURAL-CALIBRATION |
| Exact finite product factorization | DEFERRED |
| FLT7 theorem or global descent closure | OUT-OF-SCOPE |

## 16. Verification

成功した build:

```text
lake build DkMath.NumberGeometry.Phase.SevenTreasure
lake build DkMath.NumberGeometry
lake build DkMath.FLT.Seven.NumberGeometryFourteenPhaseBridge
lake build DkMathTest.NumberGeometry.SevenTreasureAxiomAudit
lake build DkMath
```

`SevenTreasureAxiomAudit` の `#print axioms` は、確認対象について
`propext`、`Classical.choice`、`Quot.sound` など既存 logical infrastructure の
みを示し、新規の `axiom`、`sorryAx`、`unsafe`、`sorry`、`admit` は追加していない。

`git diff --check` と malformed docstring / forbidden construct scan も実施する。

## 17. NGEO-013 proposed scope

次 checkpoint では、必要なら generic `FourteenPhase` の phase interpretation と
既存 carrier の coordinate/sector API の間に、さらに一方向の bounded bridge を
追加する。ただし、FLT7 の未解決 branch、global phase dynamics、または finite
sector facts からの global theorem は scope に含めない。

NGEO-012 はここで終了する。
