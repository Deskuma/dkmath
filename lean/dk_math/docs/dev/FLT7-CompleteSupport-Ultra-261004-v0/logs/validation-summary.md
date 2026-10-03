# FLT7 Complete-Support validation log index

Date: 2026-10-04 (Asia/Tokyo). Lake cwd: `lean/dk_math`.
Lean/Mathlib `v4.34.1`; initial HEAD `cf7df8206`.
Raw command output is saved alongside this index. The repository ignores `*.log`;
this Markdown index records the results in a versionable file.

| Command/check | Result | Raw log |
| --- | --- | --- |
| Initial branch/HEAD/tree, compiler and source endpoint audit | Requested branch, clean initial tree, current APIs verified | `audit-001.log` |
| `lake build DkMath.FLT.Seven.CurrentCarrierRamifiedObstruction` | Exit 0, 9188 jobs | `current-ramified-focused.log` |
| `lake build DkMath.FLT.Seven.CurrentCarrierNormalizedPower` | Exit 0, 9189 jobs | `normalized-focused.log` |
| `lake build DkMath.FLT.Seven.CurrentSupportObstruction` (final) | Exit 0, 9190 jobs | `current-support-focused-final.log` |
| `lake build DkMathTest.FLT.CompleteSupportDRCBridgeAudit` | Exit 0, 9186 jobs | `drc-bridge-focused.log` |
| `lake build DkMathTest.FLT.CurrentCompleteSupport DkMathTest.FLT.CompleteSupportDRCBridgeAudit DkMath.FLT.Seven DkMath.FLT.Prime` | Exit 0, 9334 jobs | `current-regression-facades-final.log` |
| `lake build` | Exit 0, 10350 jobs | `full-build.log` |
| `lake build DkMathTest` | Exit 0, 10942 jobs | `full-test-build.log` |
| All 36 new public production endpoint axiom lists | Standard axioms only | `current-regression-facades-final.log` |
| Three imported neutral theorem axiom lists | Standard axioms only | `current-regression-facades-final.log` |
| Six DRC calibration/address axiom lists | Standard axioms only | `drc-bridge-focused.log` |
| New implementation/test forbidden-construct scan | No matches | Checked by repository-local Python scan |
| `git diff HEAD --check` and new-file `--no-index --check` | No whitespace diagnostics | Checked after source/report edits |

Standard axiom set: `propext`, `Classical.choice`, `Quot.sound` (or subsets).
No project axiom or `sorryAx` occurs in any newly audited endpoint.

Additional recovery logs: `current-ramified-scratch.log`,
`current-prime-below-scratch.log`, `current-ramified-axioms.log`,
`normalized-axioms.log`. The earlier successful raw support check is saved as
`current-support-focused.log`; the first failed regression elaboration is saved
as `current-regression-facades.log`. The final logs above are completion evidence.

The optional checkpoint commit was rejected by automatic approval review,
stating commits are prohibited for the authorized task. Files were saved
without bypassing the rejection.
