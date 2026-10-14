# Facade closeout report — 2026-10-14

**CLOSEOUT READY**。指定の Facade/test/CI wiring と5 local commandsが全て成功した。研究はpauseのままであり、新しい数論定理や proof 修正は行っていない。

## 実装・coverage

live `git diff --name-only --diff-filter=A develop...HEAD` から17 production /19 test unitsを取り出し、各 Lean file の actual import を走査して closure を検査した。9 terminal direct imports が17/17をcover（8 transitive）。Suiteには19/19をdirect importし、さらに主幹-only smokeをimportした。source-only audit2件を落としていない。local production import graphはacyclic、production→test importはない。

Seven.leanとDkMathTest.leanには各1 importのみを追加。DkMath/FLT/Prime.lean、DkMath/FLT.lean、DkMath.lean、DkMath.Libは変更していない。既存root pathを確認し、17 production /19 original testsは全て HEAD とbyte-identicalだった。

CI YAMLをPyYAML BaseLoaderでparseし、pull_request trigger、contents:read permissions、existing lean-action inputsを保持していることと、同じjobの直後に exact suite commandがあることをassertした。lake の後続stepでの利用は [lean-action v1 metadata](https://raw.githubusercontent.com/leanprover/lean-action/v1/action.yml) と [install_elan script](https://raw.githubusercontent.com/leanprover/lean-action/v1/scripts/install_elan.sh) で確認した（elan binをGITHUB_PATHへ登録する）。これは remote CI 実行の証拠ではない。

## Local verification

Lean4.34.1 / Lake5.0.0-src+5045d00。記載秒数はsubprocess開始から終了までのmonotonic wall time。cache replayと必要なbuildを含む。

| Command (cwd: lean/dk_math) | Exit | Seconds |
|---|---:|---:|
| `lake build DkMath.FLT.Seven.ModFortyTwoAllocationSieveFacade` | 0 | 14.97 |
| `lake build DkMath.FLT.Seven` | 0 | 1146.81 |
| `lake build DkMath` | 0 | 1314.28 |
| `lake build DkMathTest.FLT.Seven.ModFortyTwoAllocationSieveSuite` | 0 | 40.50 |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean` | 0 | 7.20 |

SmokeのimportはDkMath.FLT.Sevenだけ。代表5 exportsを#checkしてactual namespace/typeを確認し、#print axiomsを直接実行した。

- `DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_fortyTwo`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.sixthPowerSieved_two_prime_pow_excluded`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.sixthPowerSieved_smallCoefficient_permutation_prime_excluded`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_no_reconstruction_of_permutation_prime_core`: `[propext, Classical.choice, Quot.sound]`
- `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFour_source_prime_exclusive_valuation`: `[propext, Classical.choice, Quot.sound]`

これらにsorryAxや非標準proof axiomはない。branch17 production /19 testsと新しい3 Lean wiring filesの禁止構文scan、YAML/graph assertions、git diff --check、新規file whitespaceは成功した。既存依存warningは下記。元の対応ファイルもHEADと同一であり、closeoutで新しいsorryを追加していない。

- `DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry``
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry``
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry``
- `DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry``
- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry``

## Changes — 11 files

| File | Change |
|---|---|
| `.github/workflows/lean_action_ci.yml` | modified: targeted suite build step |
| `lean/dk_math/DkMath/FLT/Seven.lean` | modified: one facade import |
| `lean/dk_math/DkMath/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean` | new: import-only research facade |
| `lean/dk_math/DkMathTest.lean` | modified: one suite import |
| `lean/dk_math/DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveFacade.lean` | new: top-level-only smoke / axiom probes |
| `lean/dk_math/DkMathTest/FLT/Seven/ModFortyTwoAllocationSieveSuite.lean` | new: smoke plus all19 tests |
| `lean/dk_math/docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/README.md` | modified: local CLOSEOUT READY and summary link |
| `lean/dk_math/docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/ROADMAP.md` | modified: local closeout status, research pause retained |
| `lean/dk_math/docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/branch-closeout-summary-261014.md` | new: bounded research summary / full inventory |
| `lean/dk_math/docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/report-closeout-facade-261014.md` | new: verification report / change list |
| `lean/dk_math/docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/evidence/closeout-facade-verification.md` | new: compact evidence |

## Research and handoff

[branch summary](branch-closeout-summary-261014.md) に001–019のbounded results、17/19 inventory、unbounded abstract-core families、conditional source transport、derived source ledger、genuine N>1、open source→natural endpoint bridgeを総括した。README/ROADMAPはlocal validation完了後に更新し、005/017/019のOutcome Bを保持した。

[compact evidence](evidence/closeout-facade-verification.md) は実際のexit statusesとimport inventory、axiom sets、wiring hashesを記録する。raw logsはignored `logs/__closeout-*.txt`。全無関係なDkMathTest driverの実行やremote CI成功を主張していない。ローカル READY を報告して終了する。
