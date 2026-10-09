# Report 007 — public GTail integration and release audit

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Outcome B — public integration checked; Step 007 PARTIAL because the all-test-submodule gate was interrupted for cost.**

Steps 001–006 supply a reusable research instrument and conditional arithmetic receivers. Step 007 changes public imports, documentation and test discoverability only. It adds **zero mathematical theorem endpoints**. The valuation/order/Norm/unit-class/next-packet proposals remain unproved frontier targets.

## Exact changed paths and exposure

Paths relative to `lean/dk_math`:

- `DkMath/Lib.lean`: five explicit imports, GTailSelection/Factor/Transport/Seven/SevenArithmetic under DkMath.Lib.Cosmic.
- `DkMath/FLT/Seven.lean`: two explicit imports, GTailBridge and GTailConstraintAudit, with one conditional-receiver comment.
- `DkMathTest.lean`: eight explicit imports (six existing focused tests and two new separate facade tests).
- `DkMathTest/CosmicFormula/GTailLibFacade.lean`: only import DkMath.Lib; eight real proof examples, representative public axiom checks.
- `DkMathTest/FLT/Seven/GTailFacade.lean`: only import DkMath.FLT.Seven; five real proof examples, representative public axiom checks.
- `DkMath/Lib/README.md`: exact direct list and selective/factor/transport/seven/arithmetic contracts; fixes direct-vs-transitive IdealPowerFactor coverage.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/README.md`: replaces initial planning status with checked results/public entrances/frontier links.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`: actual completion/build scope recorded at closeout.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-007.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-007.md`

No arithmetic owner proof, original focused test or constraint-ledger-006 byte is changed. Existing root DkMath.lean already imports Lib and FLT; FLT.lean already imports Seven, so neither needs a new import. The existing MIT headers and import-before-print/docs style are preserved, including in both new test files.

## Public paths and dependency audit

| Entrance | Direct imports before/after | Recursive source names before/after | Change |
| --- | --- | --- | --- |
| DkMath.Lib | 24 / 29 | 8809 / 8814 | exactly the five new neutral modules |
| DkMath.FLT.Seven | 198 / 200 | 9144 / 9152 | two owners, five neutral modules and existing GTailPascal |
| DkMathTest root driver | 107 / 115 | 9479 / 9577 | eight direct entries; 98 newly reachable names due to facade smoke graph |

Closure counts use comment-free module headers (including public/private/meta imports), not documentation examples or trailing-comment words. They are parsed source names, not job counts or kernel-status claims. The initial lexical count was refined before this final report; the reproducible audit is local audit_imports.py. The Lib closure contains **zero DkMath.FLT modules**. A DFS cycle check passed for 796 local production/test modules in the three entrance closures. Modified import lists are duplicate-free. The new owners import small neutral APIs/Basic, never Seven itself; test modules are downstream of facades, with no production import of tests. Complete before/after lists are retained locally in `.lake/build/gtail-step007/before.json` and `after.json`.

Explicit coverage matches the existing plain-import convention; no declaration is renamed and no export aliases or supplied witnesses are added. The conditional Fermat/packet results remain owner-specific even though the Seven entrance exposes them.

## Final theorem family inventory

All Step 001–006 public mathematical endpoints are retained unchanged:

| Family/source | Definitions | Public theorem endpoints | Public entrance |
| --- | --- | --- | --- |
| [GTailSelection](../../../DkMath/Lib/Cosmic/GTailSelection.lean) | 3 | 10 | `DkMath.Lib` |
| [GTailFactor](../../../DkMath/Lib/Cosmic/GTailFactor.lean) | 3 | 16 | `DkMath.Lib` |
| [GTailTransport](../../../DkMath/Lib/Cosmic/GTailTransport.lean) | 2 | 12 | `DkMath.Lib` |
| [GTailSeven](../../../DkMath/Lib/Cosmic/GTailSeven.lean) | 0 | 15 | `DkMath.Lib` |
| [GTailSevenArithmetic](../../../DkMath/Lib/Cosmic/GTailSevenArithmetic.lean) | 0 | 5 | `DkMath.Lib` |
| [GTailBridge](../../../DkMath/FLT/Seven/GTailBridge.lean) | 0 | 4 | `DkMath.FLT.Seven` |
| [GTailConstraintAudit](../../../DkMath/FLT/Seven/GTailConstraintAudit.lean) | 0 | 4 | `DkMath.FLT.Seven` |
| **Total** | **8** | **66** | **58 neutral, 8 FLT7 owner endpoints** |

Definitions are selectedTerm/Body/Gap, activeSelectedIndices/selectedResidual/coeffGCD, sumMovedIn/Out. Private proof helpers are excluded from endpoint counts. Exact signatures remain in the linked owners and corresponding report-001 through report-006.

### DkMath.Lib.Cosmic.GTailSelection

`selectedGap_add_selectedBody`, `selectedBody_empty`, `selectedGap_empty`, `selectedGap_full`, `selectedBody_full`, `selectedBody_complement`, `selectedGap_complement`, `selectedBody_singleton`, `selectedGap_Ico`, `selectedBody_Ico`.

### DkMath.Lib.Cosmic.GTailFactor

`mem_activeSelectedIndices`, `selectedBody_eq_monomial_mul_residual`, `selectedBody_eq_min_max_mul_residual`, `monomial_dvd_selectedBody`, `coeffGCD_empty`, `coeffGCD_dvd_choose`, `dvd_coeffGCD_iff`, `dvd_selectedResidual_of_dvd_coeff`, `coeffGCD_dvd_selectedBody`, `coeffGCD_eq_one_of_zero_mem`, `coeffGCD_eq_one_of_self_mem`, `coeffGCD_mul_monomial_dvd_selectedBody`, `activeSelectedIndices_interior`, `coeffGCD_eq_prime_of_interior`, `coeffGCD_prime_interior`, `prime_mul_coords_dvd_selectedBody_interior`.

### DkMath.Lib.Cosmic.GTailTransport

`selectedBody_transport`, `selectedGap_transport`, `selected_balance_transport`, `selectedBody_insert`, `selectedGap_insert`, `selectedBody_erase`, `selectedGap_erase`, `selected_insert_of_mem`, `selected_insert_of_lt`, `selected_erase_of_lt`, `selectedBody_Ico_split_at`, `selected_modEq_of_dvd_moved`.

### DkMath.Lib.Cosmic.GTailSeven

`GTail_seven_six`, `GTail_seven_five`, `selectedBody_seven_six`, `selectedBody_seven_five`, `selectedGap_seven_interior`, `selectedBody_seven_interior_eq_mul_residual`, `coeffGCD_seven_interior`, `seven_mul_coords_dvd_selectedBody_interior`, `selectedResidual_seven_interior`, `selectedBody_seven_interior`, `add_pow_seven_eq_gap_add_interior`, `add_pow_seven_sub_endpoints`, `selectedSeven_zero_endpoint_transport`, `coeffGCD_seven_zero_endpoint`, `quadratic_form_four_mul`.

### DkMath.Lib.Cosmic.GTailSevenArithmetic

`coprime_left_seven_quadratic`, `coprime_right_seven_quadratic`, `coprime_sum_seven_quadratic`, `coprime_product_seven_quadratic`, `gtail_seven_exact_seven_layer`.

### DkMath.FLT.Seven.GTailBridge

`gtail_seven_shell`, `gtail_seven_defect`, `gtail_seven_eq_of_fermat7Equation`, `gtail_seven_eq_of_counterexamplePack`.

### DkMath.FLT.Seven.GTailConstraintAudit

`fermat7_focused_bounds`, `focused_gap_lt_coordinates`, `exists_positive_focused_gap`, `seven_dvd_focused_gap`.

## Staged builds and resource scope

Commands are issued in staged incremental invocations from `lean/dk_math`, with process-local `LEAN_NUM_THREADS=2` (the interruption cleanup exception is described below); no clean build, dependency/configuration change or memory/swap change. Initial live host RAM was ~31 GiB total/~22 GiB available, with ~63 GiB swap. Missing standard cgroup memory paths prevent treating that reading as a measured container limit. No peak RSS claim is made.

Raw logs and machine-readable command/exit/duration rows are local `.lake/build/gtail-step007/*.log` / `runs.json`. The successful `+DkMath.Lib` and `+DkMath.FLT.Seven` markers explicitly request existing module targets; the attempted `+DkMathTest` was rejected and repaired using file elaboration. Durations are elapsed wall time of the corresponding invocation.

| Command | Exit | Seconds | Jobs / scope | Local raw log |
| --- | --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailSelection DkMathTest.CosmicFormula.GTailSelection` | 0 | 1.43 | 1047 | `01-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailFactor DkMathTest.CosmicFormula.GTailFactor` | 0 | 1.41 | 1063 | `02-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailTransport DkMathTest.CosmicFormula.GTailTransport` | 0 | 1.38 | 1068 | `03-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailSeven DkMathTest.CosmicFormula.GTailSeven` | 0 | 1.41 | 1069 | `04-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailSevenArithmetic` | 0 | 1.43 | 1060 | `05-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailBridge` | 0 | 7.92 | 8932 | `06-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailConstraintAudit DkMathTest.FLT.Seven.GTailConstraintAudit` | 0 | 8.18 | 8936 | `07-focused.log` |
| `LEAN_NUM_THREADS=2 lake build +DkMath.Lib` | 0 | 13.30 | 8957 | `08-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailLibFacade` | 0 | 13.42 | 8958 | `09-lib-smoke.log` |
| `LEAN_NUM_THREADS=2 lake build +DkMath.FLT.Seven` | 0 | 14.29 | 9295 | `10-seven.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFacade` | 0 | 13.89 | 9296 | `11-owner-smoke.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath` | 0 | 20.91 | 10458 | `12-wide-production.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest` | -15 (SIGTERM); session 130 | 1215.89 | incomplete; 400 test modules logged | `13-wide-test.log` |
| `LEAN_NUM_THREADS=2 lake build +DkMathTest` | 1 | 1.04 | rejected root module target | `14-test-driver.log` |
| `LEAN_NUM_THREADS=2 lake lean DkMathTest.lean` | 0 | 30.08 | edited root file and imports | `15-driver-lean.log` |

The optional all-submodule run was interrupted via the execution session's Ctrl-C after more than 15 minutes; the runner session returned 130. The Lake child continued after the runner ended, so that session status is **not a normal Lake build exit**. The lingering exact `lake build DkMathTest` process was then identified by same UID, exact command and repository cwd, terminated with SIGTERM, and absence of that build/compile process was confirmed. The surviving wrapper subsequently recorded the Lake subprocess return code **-15 (SIGTERM)** and 1215.89s elapsed. Its delayed summary write overwrote the later two command rows; those rows were restored from the recorded command results and retained raw logs. The unrelated editor `lake serve` / `lean --server` processes were preserved.

Its final raw log contains 400 distinct completed/replayed DkMathTest module names of the 683-file glob, including an unchanged Legendre calibration taking 67s. No compiler error was reported before termination, but the remaining suite is **not validated**. This is a cost stop, not a diagnosed compilation failure or RAM exhaustion. The build invocations were issued in stages; the unexpected lingering child temporarily overlapped the 30.08s edited-driver check before cleanup. No claim of strict process-level serialization is made for that interruption interval.

`lake build +DkMathTest` failed with unknown module (exit 1, 1.04s), because the configured submodule-only glob excludes that root as a build target. Corrected to the documented `lake lean DkMathTest.lean`, which builds the file's imports and elaborates it without changing configuration: **exit 0, 30.08s**, ending with `file: DkMathTest`. The edited root file is therefore checked independently of the incomplete all-submodule gate.

Lake configuration matters: DkMath library defaults to Glob.one(DkMath), so `lake build DkMath` builds its root/import closure, not all standalone production files. DkMathTest uses `DkMathTest.+`, selecting all submodule source files but excluding root DkMathTest.lean; the modified driver therefore also needs file elaboration via `lake lean DkMathTest.lean`. Successful entrance builds must not be described as a clean rebuild or an audit of every unrelated declaration. The corrected DkMath root source closure has 10314 recursive names and 1534 local production modules. The configured all-test-submodule glob covers 683 Lean files. The separate edited driver has 9577 recursive source names. These counts include external terminal names but not implicit compiler/native dependencies.

## Regression and axiom evidence

All six original focused test modules pass. The Lib smoke proves selected balance, generic forced monomial extraction, prime interior coefficient gcd and body divisor, conditional modular transport, degree-seven square balance, Q-coprimality and the (g,c)=(14,2) exact-seven-layer example solely through DkMath.Lib.
The separate owner smoke proves the general nonvacuous shell, its satisfiable (2,3,4,1) instance, the conditional natural adapter, positive focused-gap theorem type and seven-divisibility theorem type solely through DkMath.FLT.Seven. It fabricates no positive Fermat solution.

All **66/66** public endpoints were re-observed in the successful focused runs, and twelve representative endpoint checks run in the new facade tests. Parsed axiom sets:

- 63 endpoints: `[propext, Classical.choice, Quot.sound]`.
- coprime_left_seven_quadratic and coprime_right_seven_quadratic: `[propext, Quot.sound]`.
- quadratic_form_four_mul: `[propext]`.

No sorryAx or extra axiom occurs in any of these endpoint dependency lists. Local `axioms.json` stores each full name/list. Axiom lists describe these endpoints, not all unrelated declarations loaded by a broad facade.

## Existing broad research warnings

Seven and the broad production entry replay existing `declaration uses sorry` warnings in unchanged research sources:

- DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean
- DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean
- DkMath/NumberTheory/GcdNextResearch.lean
- DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
- DkMath/CosmicFormula/TriominoFLT.lean (broad production entry)

These are outside this checkpoint and untouched. The new public endpoints do not inherit sorryAx, and the new smoke sources themselves produce no warning/error. A green broad compile is not a claim that the historical research workspace contains no holes.

## Source and whitespace review

The seven mathematical owners and both new smoke sources were scanned for whole-word sorry/admit/axiom/unsafe, False.elim/exfalso and FLT impossibility patterns: no matches (rg exit 1, expected empty search). Direct Lib owner-import scan is empty and the transitive audit above excludes every DkMath.FLT module. The mathematical owner files are unchanged versus the initial HEAD.

`git diff --check` initially caught the changed project README Base line's inherited Markdown hard-break spaces. Removed the trailing spaces from that changed line; final `git diff --check` exits 0. A separate final-newline/trailing-whitespace review includes the new untracked test/docs contents; unchanged intentional Markdown hard-break lines are retained.

## Lean結果からの気づき・example・実装候補

1. **確認済みの統合結果:** 中立入口だけから選択、因子、輸送、次数7、算術の各APIを実際のexampleで使えました。FLT7入口のshellもFermat仮定なしで使えます。公開入口の統合は、以前の定理の仮定を強めたり算術的内容を増やしたりしていません。
2. **確認した意味上の境界:** 移動項の整除仮定を持つmodular transportと、原始入力のQ-coprimalityは別のAPIです。前者の保存を後者のgcd保存へ読み替える根拠はありません。smoke exampleでもこれらを独立の契約として適用しています。
3. **依存コストに関する観察:** 新たなowner公開入口テストによりテストdriverの到達名が98増えました。一方、狭いGTailConstraintAuditとGTailSevenArithmeticの直接入口は維持されています。研究中の局所試行では直接import、公開契約の回帰にはfacade smokeという使い分けが可能です。今回の増分ビルド時間だけから一般的な性能向上・悪化は推論しません。
4. **試したexample:** Lib入口から(g,c)=(14,2)の7整除・49非整除を適用し、owner入口から(a,b,c,g)=(2,3,4,1)の非空虚shellを適用しました。focused-gapの正のFermat仮定は型検査にとどめ、存在する解を偽って作っていません。
5. **次の実装提案（未実施）:** 付値保存式を試す際は正確な非零性と端点単元を持つ小さい直接import校正から始め、既存境界gcdが要求するCoprime g cを別途証明してください。q²配分、21整除、Norm/UnitGaugeのtyped transport、次候補構成は[report-006.md](report-006.md)と[constraint-ledger-006.md](constraint-ledger-006.md)の未証明候補のままです。今回それらの数学的探索・定理実装を再開していません。
6. **テスト入口の提案（確認結果から）:** Lakeのサブモジュールglobとルートdriverは異なる検証範囲です。今後も全テストサブモジュールと編集したdriverを区別して確認すると、公開import回帰がどちらに含まれるか明確になります。今回この差をコード設定変更で隠していません。

## Engineering decision and stop

The public integration/frontdoor/focused gates, DkMath production entrance and edited root test-file elaboration pass, with 66 endpoint axiom lists on standard foundations. **Step 007 remains PARTIAL**: the 683-file all-test-submodule gate did not finish within the bounded broad-test attempt. This is an honest coverage gap, not an integration dependency failure; Outcome C is not assigned to an interrupted, error-free attempt.

A narrowly scoped engineering PR for these GTail public imports/docs/tests can be proposed with this explicit validation gap; full Step 007 / whole-suite engineering release acceptance is not signed off. Completing the broad test gate is still needed for that stronger acceptance. Neither statement endorses FLT7 closure. No PR or merge is performed in this checkpoint.

Outcome B preserves the arithmetic frontier: exact v7(g), q² allocation, order-21, typed Norm/unit-power class transfer and constructive next CounterexamplePack remain open. Smaller g alone is not a descent provider. Stop after the final integration evidence and docs; no new arithmetic theorem, branch operation or external proof search.
