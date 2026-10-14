# 013 verification summary

Date: 2026-10-14. Provenance: Codex がこの checkout で実行した tool 出力を要約。独立した第三者再検証ではない。作業再開後の再実行結果を記録する。Raw logs は保存対象外。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual result |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport` | exit 0; `Build completed successfully (9088 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean` | exit 0; examples and named regression accepted |
| `#print axioms` for three exports and regression | each: propext, Classical.choice, Quot.sound; no sorryAx |
| forbidden construct `rg` over the two new Lean files | no matches (rg exit 1) |
| `git diff --check` | exit 0 |

Audited declarations:

- `DkMath.FLT.Seven.centeredSevenSextic_not_dvd_thirteen`
- `DkMath.FLT.Seven.centeredSevenSextic_no_image_of_thirteen_support`
- `DkMath.FLT.Seven.nestedAllocation_excluded_of_thirteen_support`
- `DkMathTest.FLT.Seven.allocationThree_thirteenSupport_regression`

Proof provenance: kernel-checked `decide` on the universal ZMod13 statement, followed by arbitrary-natural cast reduction. Python discovery in the instruction is not a proof dependency; no Python mathematical precheck was run in this gate.

SHA256 (relative to working directory):

```text
91e6a7d6fdbedcea2500baaf423aa0753f7852e5a3028058b5252a5351a9b8e0  DkMath/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean
353a27b790220588b0514d8f0bfaa2aaca0e2fc0c8842b2e147c4d3bb678da52  DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean
```

The regression concerns only r=3 at M=3*13^12; no full-sieve emptiness is asserted.
