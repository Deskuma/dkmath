# Facade closeout verification — 2026-10-14

Status: **CLOSEOUT READY (local)**。Provenance: Codexが現在のworking checkoutで実行したtool出力の要約。第三者の独立再検証でもGitHub CIの成功結果でもない。

Snapshot before closing edits:

```text
HEAD: a982773ac9c5d4a7463bdcaf5739960f10696d0b
develop: b0ffe44c989bb78a8dabb7e47051fe964ba87e5a
```

Git compare `develop...HEAD` の added paths をDkMath/FLT/SevenとDkMathTest/FLT/Sevenに限定してinventoryを生成し、live source importsの推移閉包と照合した。Closing filesはworking-tree changesとして検証した。

## Observed commands

| Command (cwd: lean/dk_math) | Exit | Seconds |
|---|---:|---:|
| `lake build DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade` | 0 | 14.97 |
| `lake build DkMath.FLT.Seven` | 0 | 1146.81 |
| `lake build DkMath` | 0 | 1314.28 |
| `lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite` | 0 | 40.50 |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean` | 0 | 7.20 |

Success endings: production facade 9106 jobs; Seven 9313 jobs; DkMath10476 jobs; suite9334 jobs。各job数は実logのsuccess endingから取得した。

## Import assertions

- Production17/17=9direct+8transitive。Local import closureにcycleなし。
- Suite19/19 direct +new smoke。Smoke imports exactly `[DkMath.FLT.Seven]`。
- DkMath root→FLT→Seven→research facade を確認。
- DkMathTest root→suite→all19 tests/smoke を確認。
- Production closureにDkMathTest importなし。
- Original17 production+19 testsはHEADとbyte-identical。

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

Test modules: all19 direct (namespace DkMathTest.FLT.Seven):

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

## Axioms / baseline warnings

Actual direct smoke #print output:

- `DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_fortyTwo`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.sixthPowerSieved_two_prime_pow_excluded`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.sixthPowerSieved_smallCoefficient_permutation_prime_excluded`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_no_reconstruction_of_permutation_prime_core`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_source_prime_exclusive_valuation`: `[propext, Classical.choice, Quot.sound]`

sorryAxなし。17/19 branch filesとnew3 Lean filesのsorry/admit/axiom/unsafe/native_decide scanは一致なし。

Broad aggregator dependencies emitted these existing warnings:

- `DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry``
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry``
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry``
- `DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry``
- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry``

これらはbranch export auditとは別範囲。Global historical DkMath environment全体がaxiom-freeとの主張はしていない。

## CI / final structural checks

PyYAML parse + assertions: PASS。PR trigger・job permissions・test:falseを保持し、同じjobのlean-action後にsuite build stepがある。公式 [action metadata](https://raw.githubusercontent.com/leanprover/lean-action/v1/action.yml) / [elan setup](https://raw.githubusercontent.com/leanprover/lean-action/v1/scripts/install_elan.sh) のGITHUB_PATH登録を確認。実remote CIは未実行。

`git diff --check`: exit0。New file whitespace: PASS。Raw logs remain ignored and are not archived in evidence。

SHA256 of six wiring files:

```text
9d74f8a76ae84cc977b4711a16767e237e4884e9af0543552fb909616e0f4ff5  .github/workflows/lean_action_ci.yml
e1569a281415c1eb0a0b13505c17d32af920cc4dc40df03f4446940ae6b7684e  lean/dk_math/DkMath/FLT/Seven.lean
9f689997b2022935c3467037dc53018c516893c7e45c926d22c1e7ff71305dde  lean/dk_math/DkMath/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean
9e88de676090fc5db969ec87f7b9217c84729be7252bcd0ce9eb2d6f407cdb59  lean/dk_math/DkMathTest.lean
c8fd950fc8229d8a1e5765fb4f27432b309ef616c7a100464cf39cd0b06bd73f  lean/dk_math/DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean
7d6b1c5a82cd366dcff2422ce6b42530a74be08773e2c99cf3b25ec626d141f0  lean/dk_math/DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveSuite.lean
```
