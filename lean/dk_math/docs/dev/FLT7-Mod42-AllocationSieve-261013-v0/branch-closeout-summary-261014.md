# FLT7 Mod42 Allocation Sieve — branch closeout summary

2026-10-14。**CLOSEOUT READY**（ローカル接続・検証完了、CI coverage 設定済み）。GitHub CI の実行結果ではない。研究は gate019 で pause し、この closeout は gate020 ではない。

## 研究結果と境界

出発点は、legitimate divisor r の両 exact GN/RHS allocation receiver から M/r≡1 (mod42) を導く必要条件だった。endpoint-free cheap filter を分離し、cheap 通過が exact receiver の存在を意味しないことを countermodels と bounded/unbounded families で検証した。M=589 の adjacent integer-image bracket も exact receiver の排除を与えた。

actual centeredSevenSextic の法5値域障害を general gap/divisor に拡張し、法13では unit gap と complementary13 support が両 exact receiver を排除した。さらに七乗差の ring identity と有限体の7乗写像の単射性から、odd prime ℓ と Coprime 7 (ℓ−1) の十分条件を形式化した。receiver consumer は固定因子7のためℓ≠7を保持する。法11・13の成立と法29・2の反例を検証し、modular zero を exact endpoint witness と混同していない。

primitive allocation の実際の quotient coprimality と strict size から、M=c*p^n,c≤343 の eligible divisor では p∤r、n>0ならp∣M/rを証明した。これと polynomial image obstruction を接続し、条件付きの unbounded abstract-core exclusion families を得た。2*13^(6+4*k) と3*13^(k+1) には distinct-core の単射性も検証済み。有限 bounded progression と fixed composite diagnostics は、それぞれの成立範囲を保持する。

actual source p への接続は `internalDepthFourSeventhCore p=c*ℓ^n` を明示した conditional obstruction である。この factorization を bare p から証明したとは主張しない。source の M*N=V*C、coprimality、prime valuation conservation/exclusive ownership は既存 source facts の派生 readout。gate019 の N>1 は actual quadratic cubic-coordinate constraints を使う source-only test theorem だが、M 単独の新しい分類ではない。M=29²,N=1 の scalar model は actual packet ではなく、N=1 をそのまま actual complement にすることはできない。

**Open:** same-packet source→primitive natural additive endpoints/chart の存在は未供給。gate005/017の constructive bridge とgate019の M-only sharpening は Outcome B のまま。全 actual M の排除、packet 不存在、unconditional FLT7 closure は得ていない。追加の弱い sieve gates を自動的に始めず、独立 source constraint に関する戦略再検討を維持する。

## 接続

- [Production facade](../../../DkMath/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean): 9 direct imports で17 production unitsをcover。
- `DkMath.FLT.Seven` に1 import。既存 DkMath→DkMath.FLT→DkMath.FLT.Seven の path を確認。
- [Public smoke](../../../DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean): import は DkMath.FLT.Seven のみ。
- [Test suite](../../../DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveSuite.lean): smoke +19 branch testsを全て direct import。DkMathTest に1 suite import。
- CI は existing lean-action step 後にこの exact suite の lake build を追加。既存 triggers、permissions、test:false を保持し、無関係な全 test driver は有効化していない。

## Local checks

| Command (cwd: lean/dk_math) | Exit | Seconds |
|---|---:|---:|
| `lake build DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade` | 0 | 14.97 |
| `lake build DkMath.FLT.Seven` | 0 | 1146.81 |
| `lake build DkMath` | 0 | 1314.28 |
| `lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite` | 0 | 40.50 |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean` | 0 | 7.20 |

代表5 exports の #check/#print axioms は主幹 import から成功。公理は全て propext、Classical.choice、Quot.sound。17 production /19 tests の禁止構文 scan は一致なし。元の36ファイルはHEADとbyte-identical。Import closure、YAML syntax/step、diff/whitespace を検査した。

広い既存 aggregator の依存には以下の既存 sorry 警告がある。今回の研究 exports の sorryAx-free audit と区別し、root全体がaxiom-freeとは主張しない。

- `DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry``
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry``
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry``
- `DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry``
- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry``

## Production inventory — 17/17

Git compare `develop...HEAD` の added files と live imports から機械的に検査した。direct=9、transitive=8。

| Production unit (DkMath.FLT.Seven) | Facade reach |
|---|---|
| `SevenRamifiedFusionCenteredImage589` | direct |
| `SevenRamifiedFusionCenteredModFiveImage` | direct |
| `SevenRamifiedFusionCenteredThirteenSupport` | transitive |
| `SevenRamifiedFusionCompositeCore9653618` | direct |
| `SevenRamifiedFusionGeneralGapModFiveImage` | transitive |
| `SevenRamifiedFusionModFortyTwoAllocationSieve` | transitive |
| `SevenRamifiedFusionModFortyTwoCheapAllocation` | transitive |
| `SevenRamifiedFusionModFortyTwoCheapBoundaryAudit` | transitive |
| `SevenRamifiedFusionModSixResidues` | transitive |
| `SevenRamifiedFusionParametricMixedExclusion` | direct |
| `SevenRamifiedFusionPermutationPrimeSupport` | transitive |
| `SevenRamifiedFusionPrimePowerPrimitiveExclusion` | direct |
| `SevenRamifiedFusionSmallCoefficientPrimePowerOwnership` | direct |
| `SevenRamifiedFusionSmallCoefficientPrimeSupport` | transitive |
| `SevenRamifiedFusionSourcePermutationPrimeObstruction` | direct |
| `SevenRamifiedFusionSourcePrimeValuationLedger` | direct |
| `SevenRamifiedFusionThirteenPowerPrimitiveExclusion` | direct |

## Branch test inventory — 19/19

全て suite の direct import。下記の source audit と source constraint separation は test-only であり production に import しない。新しい smoke とsuite自身は19件に含めない。

- `SevenRamifiedFusionCenteredImage589`
- `SevenRamifiedFusionCenteredModFiveImage`
- `SevenRamifiedFusionCenteredThirteenSupport`
- `SevenRamifiedFusionCompositeCore9653618`
- `SevenRamifiedFusionGeneralGapModFiveImage`
- `SevenRamifiedFusionModFortyTwoAllocationSieve`
- `SevenRamifiedFusionModFortyTwoCheapAllocation`
- `SevenRamifiedFusionModFortyTwoCheapBoundaryAudit`
- `SevenRamifiedFusionModSixResidues`
- `SevenRamifiedFusionParametricMixedExclusion`
- `SevenRamifiedFusionPermutationPrimeSupport`
- `SevenRamifiedFusionPrimePowerPrimitiveExclusion`
- `SevenRamifiedFusionSmallCoefficientPrimePowerOwnership`
- `SevenRamifiedFusionSmallCoefficientPrimeSupport`
- `SevenRamifiedFusionSourceAllocationChartAudit`
- `SevenRamifiedFusionSourceConstraintSeparation`
- `SevenRamifiedFusionSourcePermutationPrimeObstruction`
- `SevenRamifiedFusionSourcePrimeValuationLedger`
- `SevenRamifiedFusionThirteenPowerPrimitiveExclusion`

## Handoff

ローカル closeout は READY。CI workflow coverage は設定済みだが remote run は未実行。ユーザー側の integration/push と、その後の develop PR 上の独立した実CI結果を区別する。[closeout report](report-closeout-facade-261014.md) と [verification evidence](evidence/closeout-facade-verification.md) を参照。ここで終了する。
