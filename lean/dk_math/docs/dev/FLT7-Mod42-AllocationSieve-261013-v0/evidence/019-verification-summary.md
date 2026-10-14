# 019 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した tool 出力の要約。第三者による独立再検証ではない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMathTest.FLT.Seven.SevenRamifiedFusionSourceConstraintSeparation` | exit 0; 9088 jobs |
| new Lean forbidden construct scan | rg exit 1; no matches |
| final build log warning/error/sorry scan | rg exit 1; no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Calibration initially failed twice due to absent Nat.mul_eq_one_iff / Nat.mul_eq_one names. Corrected calibration using global mul_eq_one exited0. Final test build exited0; no hypotheses strengthened to repair compilation.

Build ending:

```text
Build completed successfully (9088 jobs).
```

Explicit `#print axioms` in namespace `DkMathTest.FLT.Seven`:

| Declaration | Axioms |
|---|---|
| scalarLedger29Squared | propext |
| primeDivisor29Squared | propext, Classical.choice, Quot.sound |
| scalarLedger_no_permutation_prime | propext, Classical.choice, Quot.sound |
| sourceComplement_ne_one | propext, Classical.choice, Quot.sound |
| actualSourceComplement_gt_one | propext, Classical.choice, Quot.sound |

No sorryAx. The scalar arithmetic is kernel-checked decide; universal prime classification uses prime power divisibility. The source result uses cubic polynomial factorization, signed cubic difference, actual source A/B/A+B nonzero facts and existing complementary root extraction.

Signature probes in the test check actual coordinate coprimality, quadratic norm, signed B identity, both cubic source norms, signed root gap, normalized axis difference, conditional reconstruction core bound and source exclusive valuation. Source inspection beyond these focused imports is not presented as an independent fresh build.

SHA256, relative to working directory:

```text
0ac1753d82b93c2ed702c52486553775067e1e9aaeca6b1309e63b2ea0c5f57e  DkMathTest/FLT/Seven/SevenRamifiedFusionSourceConstraintSeparation.lean
```

No production module added. Temporary logs use ignored logs/__019-*.txt filenames. The model is not an actual source packet, receiver or FLT counterexample. N>1 separates the source tuple but does not exclude actual M=841 with other complementary data. No new M-only restriction is claimed.
