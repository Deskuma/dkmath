# Step042 source inventory — terminal / lifted / ramified decision

2026-10-11。Local HEAD `2ef7a30dd97df285b31a089317ae550cd1b960a6`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。Source-only audit、fresh Lean validation ではない。

## 重要な現行 source 訂正

instruction-042 §3.4 / Candidate I と review-041 の「Row-Z extraction が open」は、
現行全 owner の状態には一致しない。TERM-009 owner は obligation を定義するが、
TERM-010 `SevenBaseTerminalRowZSignedResidualCore` が実際にその Nonempty を証明し、
canonical inhabitant / signedRamified / ramifiedChartResolution を構成済み。
「Row-Z signed extraction open」という結論を受入条件の文面だけから再掲しない。
open なのは抽出後の global terminal contradiction / primitive reconstruction / recursive closure。
指示書の作業制限は保持し、source と矛盾する事実認定だけ訂正する。

## Branch truth table

| Branch / proposition | Actual source status | What does not follow |
|---|---|---|
| Away pivot exponent=1: reconstruction seed / closure provider | **negated Nonempty is proved**。単なる未実装ではない | terminal seed 構成は採用不可。original CounterexamplePack の不存在まで証明したわけではない |
| Terminal Row-Y | swapped natural RamifiedCoordinateNormalForm y x z is inhabited | ramified terminal exclusion / FLT7 |
| Terminal Row-Sum | False is proved from actual source/profile | 他の row の排除 |
| Terminal Row-Z: signed chart / seven-divisible signed gap | proved in TERM-009 | 自動的な型変換ではない |
| Terminal Row-Z: TraceOneInt(-2) seventh-root extraction | **proved / inhabited in TERM-010**、指示書の open 判定を訂正 | original counterexample contradiction、new primitive next triple |
| Terminal surviving Y/Z → common ramified summit | inhabited、row-specific constructors available | global terminal closure |
| Away exponent≥2 | necessary valuation condition for seed。seed inhabitation is not proved by this inequality | converse two_le_pivotExponent、explicit next triple |
| FUSION visible signed roots as next signed chart | no_direct_signedFermatSevenChart proved | original hypothetical Fermat chart の矛盾 |
| FUSION internal carrier depth5→4 | depth drop proved | counterexample descent / source-indexed measure transition |
| InternalDepthFourCounterexampleReconstructionObligation | named proposition、no inhabitant supplied by boundary。**not a proved negation** | logical impossibility と断定不可。conditional later exclusions keep extra assumptions |
| CRT original integer residuals | all four divisible by combinedModulus | strict absolute bounds、zero windings、row mismatch |
| nine fixed first-coordinate residuals | exact dependent decomposition proved | 新 independent global constraints |

## Actual ownership / source types

以下は現行ファイルの signature / proof route を確認した位置。名前は特記以外
namespace `DkMath.FLT.Seven` に属する。owner basename 自体は namespace ではない。

- [Basic:16](../../../DkMath/FLT/Seven/Basic.lean): Fermat7Equation; CounterexamplePack (x y z : ℕ) : Prop with hx,hy,hz,hxy,hEq.
- [CounterexampleRouting:202](../../../DkMath/FLT/Seven/CounterexampleRouting.lean): CounterexampleRoute : Prop; counterexampleRoute_of_pack {x y z} (hPack) produces Gap/GN away split or SevenAdicCounterexamplePacket.
- [AwayValuationTransfer:61](../../../DkMath/FLT/Seven/AwayValuationTransfer.lean): AwayExceptionalCarrierSource y z carrier : Prop has right/left/sum; carrier must literally equal y/z/y+z with seven-unit guards.
- [AwayValuationTransfer:69](../../../DkMath/FLT/Seven/AwayValuationTransfer.lean): AwayValuationTransferPacket x y z : Type stores normal, carrier, source, positive carrier/root absolute value, exact valuation transfer.
- [DescentClosureAudit:17](../../../DkMath/FLT/Seven/DescentClosureAudit.lean): AwayDescentClosureProvider (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type requires nextX/Y/Z,nextPack,nextRoute,carrier_match.
- [SevenBaseTerminalDescentProvider:20](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentProvider.lean): AwayDescentReconstructionSeed {x y z} (p) : Type requires nextX/Y/Z,nextNormal,target_source; nextRoute/toClosureProvider at32/62, inverse at76.
- [SevenBaseTerminalDescentProvider:90](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentProvider.lean): Nonempty seed iff Nonempty closure provider; away_depth_descent_of_reconstructionSeed at102.
- [SevenBaseTerminalDescentSeedExclusion:16](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean): seed.two_le_pivotExponent p; terminal negations at40/49; openPacket.not_reconstructionObligation at59.
- [SevenPivotDepthPacket:13](../../../DkMath/FLT/Seven/SevenPivotDepthPacket.lean): AwaySevenPivotDepthPacket {x y z} (r) : Type: exponent>0, carrier_depth_eq, depth_eq, root_depth_eq.
- [SevenPivotDescentAudit:13](../../../DkMath/FLT/Seven/SevenPivotDescentAudit.lean): base exponent=1 versus lifted 1<exponent; lifted unit-orbit/rootFst unit/rootSnd power=0 are local results, not a new natural triple.
- [SevenBaseTerminalExclusion:15](../../../DkMath/FLT/Seven/SevenBaseTerminalExclusion.lean): RowY/Z/SumProfile terminal : Prop; row-specific endpoint, sign quotient and load identities.
- [SevenBaseTerminalFermatChartResolution:34](../../../DkMath/FLT/Seven/SevenBaseTerminalFermatChartResolution.lean): RowY.to_swapped_ramified; RowSum.false_of_swapped_away at63; signedOddPermutation at150; seven_dvd_signed_gap at170.
- [SevenBaseTerminalFermatChartResolution:195](../../../DkMath/FLT/Seven/SevenBaseTerminalFermatChartResolution.lean): SignedRamifiedCoordinateNormalForm (a b c : ℤ) : Type; signed chart + 7∣c-b + root:TraceOneInt(-2) + cyclotomicSevenToTraceOne c b=sevenAxis*root^7.
- [SevenBaseTerminalFermatChartResolution:206](../../../DkMath/FLT/Seven/SevenBaseTerminalFermatChartResolution.lean): RowZ obligation is a Type (subtype root witness), not merely a Prop; to_signed_ramified consumes an inhabitant at217.
- [SevenBaseTerminalRowZAlternatingPowerSplit:183](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZAlternatingPowerSplit.lean): positive primitive alternating split: x+y=7^6*a^7, alternating factor=7*b^7, z=7*a*b; construction at199.
- [SevenBaseTerminalRowZSignedResidualCore:97](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZSignedResidualCore.lean): axis peeling, norm=b^7, terminality, primitive signed coordinates; nonempty core at115; gcd_conj_isUnit at162.
- [SevenBaseTerminalRowZSignedResidualCore:192](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZSignedResidualCore.lean): exists_residualCore_eq_seventh_power; Nonempty RowZ obligation at211; inhabitant at223; signedRamified at233; ramifiedChartResolution at256.
- [SevenBaseTerminalRamifiedSummit:43](../../../DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean): PrimitiveRamifiedSummitPacket : Type; natural/signed row-specific summit constructors at108/162; nonempty_ramifiedSummit at232.
- [SevenRamifiedSignedRootDepth:49](../../../DkMath/FLT/Seven/SevenRamifiedSignedRootDepth.lean): RamifiedSignedRootDepthPacket : Type; balanced source, signed-root equalities, coprimality, gap/quotient roots and exact equations, unit guards, normalizedEquation.
- [SevenRamifiedSignedRootDepth:216](../../../DkMath/FLT/Seven/SevenRamifiedSignedRootDepth.lean): RamifiedRealCubicBalancedAxisSplitPacket.nonempty_signedRootDepth constructs packet from balanced input; declaring fields does not prove arbitrary source has that input.
- [SevenRamifiedFusionDirectChartObstruction:18](../../../DkMath/FLT/Seven/SevenRamifiedFusionDirectChartObstruction.lean): RamifiedSignedRootDepthPacket.signedRoot_seventhPowerDifference_eq; exact depth via sevenPowSix_not_dvd at34; not seventh power at60; no_direct_signedFermatSevenChart at84.
- [SevenRamifiedFusionStrictDescentFailureBoundary:25](../../../DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean): nested namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport; internalDepthFourCarrier and outerDepthFiveCarrier.
- [SevenRamifiedFusionStrictDescentFailureBoundary:70](../../../DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean): InternalDepthFourCounterexampleReconstructionObligation p := ∃x y z, ∃route:AwayValuationTransferPacket x y z, route.carrier=internalDepthFourCarrier p; iff strict candidate at90.
- [SevenBaseTerminalLiftedReconstruction:160](../../../DkMath/FLT/Seven/SevenBaseTerminalLiftedReconstruction.lean): SignedRepresentativePacket candidate independently centers scale/model/weighted; all parameters indexed by terminal routing, not a proof excluding exponent≥2.
- [SevenBaseTerminalLiftedReconstruction:352](../../../DkMath/FLT/Seven/SevenBaseTerminalLiftedReconstruction.lean): integerWeightedDefect uses centered weighted tuple; originalReconstructionDefect at378 uses actual root/endpoints.
- [SevenBaseTerminalLiftedReconstruction:396](../../../DkMath/FLT/Seven/SevenBaseTerminalLiftedReconstruction.lean): modulus_dvd_originalReconstructionDefect; original winding packet at615 / constructor643; integerWeightedDefect_eq_zero_of_abs_lt at682.
- [SevenBaseTerminalExclusion:171](../../../DkMath/FLT/Seven/SevenBaseTerminalExclusion.lean): DefectStrictBounds bounds integerWeightedDefect, not originalReconstructionDefect; exact_reconstruction_of_defect_strictBounds at192.
- [SevenBaseTerminalExclusion:227](../../../DkMath/FLT/Seven/SevenBaseTerminalExclusion.lean): ReconstructedRowMismatch requires row-specific False from centered reconstruction equality; receiver at251 / terminal_exclusion_of_receiver at269 remain conditional.
- [SevenBaseTerminalCellCarryDependency:99](../../../DkMath/FLT/Seven/SevenBaseTerminalCellCarryDependency.lean): fixedFirstResidual_decomposition universal+endpoint+root residual; firstCarry_eq at359; all cell carries/dependency packet are constructed, no zero-carry theorem.
- [QuadraticBridge:33](../../../DkMath/FLT/Seven/QuadraticBridge.lean): cyclotomicSevenToTraceOne (z y : ℤ) : TraceOneInt(-2), norm identity at44.
- [QuadraticEuclidean:220](../../../DkMath/FLT/Seven/QuadraticEuclidean.lean): traceOneNegTwoEuclideanDomain : EuclideanDomain (TraceOneInt(-2)).
- [QuadraticUnits:34](../../../DkMath/FLT/Seven/QuadraticUnits.lean): isUnit_iff_eq_one_or_neg_one; every unit is a seventh power at38.
- [QuadraticCoprimeFactor:26](../../../DkMath/FLT/Seven/QuadraticCoprimeFactor.lean): exists_eq_seventh_power_of_coprime_mul_eq_pow uses IsUnit(gcd x y) and x*y=z^7 in TraceOneInt(-2).
- [GTailEisensteinCyclotomicCommonReceiver:17](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean): namespace GTailCommonReceiver; C=QuadraticAlgebra R (-1) 1; fromEisenstein domain TraceOneInt(-1), fromCyclotomic domain R.
- [GTailEisensteinCyclotomicNoDirectHom:39](../../../DkMath/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean): no E(-1)→R or R→E(-1) unital hom; theorem does not address the discriminant−7 order.

`DkMath/FLT/Seven/Seven.lean` は存在せず、実際の facade は
[DkMath/FLT/Seven.lean](../../../DkMath/FLT/Seven.lean)。132–134行に TERM-010 / summit imports、
192行以降に U1.6 と追加 finite/nested/centered receiver audits を import 済み。
STATUS.md の265–300行と ROADMAP.md の578–622行はそれぞれ U1.6 未構成と TERM-010 完了を説明する。
古い更新日や途中 checkpoint の「open」は最終 source status と区別した。

## Exact signatures copied from source

以下は **source の verbatim signature**（#check の新実行結果ではない）。
`open DkMath.NumberTheory.TraceOneQuadratic` の TraceOneInt、conj、norm を用いる。
暗黙 `{...}` と明示 `(...)` を省略せず転記した。


[SevenBaseTerminalDescentProvider:90](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentProvider.lean)（nonempty_descentReconstructionSeed_iff_closureProvider）:

```lean
theorem nonempty_descentReconstructionSeed_iff_closureProvider
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    Nonempty (AwayDescentReconstructionSeed p) ↔
      Nonempty (AwayDescentClosureProvider x y z p)
```

[SevenBaseTerminalDescentSeedExclusion:16](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean)（AwayDescentReconstructionSeed.two_le_pivotExponent）:

```lean
theorem AwayDescentReconstructionSeed.two_le_pivotExponent
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r)
    (seed : AwayDescentReconstructionSeed r.cubic.transfer) :
    2 ≤ p.exponent
```

[SevenBaseTerminalDescentSeedExclusion:40](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean)（no_descentReconstructionSeed_of_exponent_eq_one）:

```lean
theorem no_descentReconstructionSeed_of_exponent_eq_one
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (hterminal : p.exponent = 1) :
    ¬ Nonempty (AwayDescentReconstructionSeed r.cubic.transfer)
```

[SevenBaseTerminalDescentSeedExclusion:49](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean)（no_descentClosureProvider_of_exponent_eq_one）:

```lean
theorem no_descentClosureProvider_of_exponent_eq_one
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (hterminal : p.exponent = 1) :
    ¬ Nonempty
      (AwayDescentClosureProvider x y z r.cubic.transfer)
```

[SevenBaseTerminalFermatChartResolution:206](../../../DkMath/FLT/Seven/SevenBaseTerminalFermatChartResolution.lean)（AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation）:

```lean
def AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (_hz : AwaySevenBaseTerminalRowZProfile terminal) : Type
```

[SevenBaseTerminalRowZSignedResidualCore:211](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZSignedResidualCore.lean)（AwaySevenBaseTerminalRowZProfile.nonempty_signedRamifiedArithmeticObligation）:

```lean
theorem AwaySevenBaseTerminalRowZProfile.nonempty_signedRamifiedArithmeticObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    Nonempty
      (AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz)
```

[SevenBaseTerminalRowZSignedResidualCore:233](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZSignedResidualCore.lean)（AwaySevenBaseTerminalRowZProfile.signedRamified）:

```lean
noncomputable def AwaySevenBaseTerminalRowZProfile.signedRamified
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    SignedRamifiedCoordinateNormalForm
      (z : ℤ) (-(y : ℤ)) (x : ℤ)
```

[SevenRamifiedFusionDirectChartObstruction:84](../../../DkMath/FLT/Seven/SevenRamifiedFusionDirectChartObstruction.lean)（no_direct_signedFermatSevenChart）:

```lean
theorem no_direct_signedFermatSevenChart
    (p : RamifiedSignedRootDepthPacket) :
    ¬ ∃ c : ℤ,
      SignedFermatSevenChart
        p.signedRightRoot (-p.signedLeftRoot) c
```

[SevenRamifiedFusionStrictDescentFailureBoundary:70](../../../DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean)（InternalDepthFourCounterexampleReconstructionObligation）:

```lean
def InternalDepthFourCounterexampleReconstructionObligation
    (p : RamifiedSignedRootRoutingPacket) : Prop
```

[SevenBaseTerminalLiftedReconstruction:396](../../../DkMath/FLT/Seven/SevenBaseTerminalLiftedReconstruction.lean)（AwaySevenBaseTerminalSignedRepresentativePacket.modulus_dvd_originalReconstructionDefect）:

```lean
theorem
    AwaySevenBaseTerminalSignedRepresentativePacket.modulus_dvd_originalReconstructionDefect
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source
```

[SevenBaseTerminalCellCarryDependency:99](../../../DkMath/FLT/Seven/SevenBaseTerminalCellCarryDependency.lean)（fixedFirstResidual_decomposition）:

```lean
theorem fixedFirstResidual_decomposition
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (u v y z : ℤ) :
    AwayFirstCoordinateIntegerResidual row column u v y z =
      awayFixedUniversalSign row column *
          AwayUniversalFstIntegerResidual u v y z +
        awayFixedEndpointCoefficient row column y z *
          AwayEndpointIntegerResidual row y z +
        awayFixedRootCoefficient row column u v *
          AwayRootIntegerResidual column u v
```

`no_direct_signedFermatSevenChart` の fully qualified namespace は
`DkMath.FLT.Seven.RamifiedSignedRootDepthPacket`。
`InternalDepthFourCounterexampleReconstructionObligation` の fully qualified namespace は
`DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport`。

## Original CRT versus independently centered weighted defect

M=family.combinedModulus=full terminal cubic-root load。actual original tuple は
`(r.cubic.rootTriple.normal.root.fst, r.cubic.rootTriple.normal.root.snd, (y:ℤ), (z:ℤ))`。
original residual はこの tuple から `(model.u*s³, model.v*s³, model.y*s⁷, model.z*s⁷)` を引いたもの。
一方 integerWeightedDefect の左側は independently centered `signed.weighted`。
差は original tuple minus centered weighted tuple であり、modulus の倍数でも zero とは限らない。

original residual を0にする独立入力は四座標それぞれ `|originalResidual_i|<(M:ℤ)`。
M divisibility と既存 scalar `integerWeightedDefect_eq_zero_of_abs_lt` によって0を得られるが、
それで得るのは **original tuple=model.weightedScale scale**。
既存 `exact_reconstruction_of_defect_strictBounds` / `ReconstructedRowMismatch` の
**signed.weighted=model.weightedScale scale** と同じ命題ではない。
original=weighted の追加 bridge、または original equality を直接受ける新 row obstruction が必要。
centered model / scale 自体の半幅 bounds は model*s³/s⁷ の積を M より小さくしない。

`fixedFirstResidual_decomposition` は signed.model の fixed residual の依存関係を与える。
original reconstruction residual とその fixed equation residual も混同しない。
Row-resolved quotient/sign/load formulas、local congruences、original/cell windings は証明済み、
windings=0、bounds、row mismatch の inhabitants は構成されていない。

## Additional downstream checks preventing stale frontier selection

SevenRamifiedFusionDepthFourReconstructionAudit:20 は reconstruction iff finiteCharts.Nonempty、
30行は reconstructed root depth3、42行は new root ≠ existing inner root、74行は ideal+powerから
全 generator coordinates を復号する万能 decoder の不存在を証明する。
これらは invariant chart extractor 全般の不存在ではない。
SevenRamifiedFusionCenteredGnomonGap:168 の reconstruction exclusion は explicit perfect-sixth
family premise を残し、source packet の False を結論していない。
finite/nested/centered reductions の再実装も Step043 の新 obstruction として採用しない。
