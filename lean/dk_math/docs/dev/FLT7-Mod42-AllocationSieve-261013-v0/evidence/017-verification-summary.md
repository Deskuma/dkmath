# 017 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した tool 出力の要約。第三者の独立再検証ではない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery` | exit 0; 9091 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean` | exit 0 |
| new Lean forbidden constructs | rg exit 1; no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Build excerpt:

```text
Built DkMath.FLT.Seven.SevenRamifiedFusionSourcePermutationPrimeObstruction (5.7s)
Build completed successfully (9091 jobs).
```

Explicit `#print axioms` on all3 exports in namespace `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport` reported `[propext, Classical.choice, Quot.sound]`:

- `internalDepthFour_no_reconstruction_of_permutation_prime_core`
- `reconstructed_core_ne_smallCoefficient_permutation_prime_power`
- `internalDepthFour_no_finiteCharts_of_permutation_prime_core`

No sorryAx. Source hcore equality is an explicit premise; no factorization is inferred from p alone.

Lean signature probes verified:

- normal form requires `pack : CounterexamplePack u (internalDepthFourCarrier p) v`;
- complementary ledger is an actual source-only existential root theorem on K;
- quotient signed-power / cell-power equivalence is logical;
- loaded absorption requires both seventh-power cell hypotheses;
- finite chart membership requires bounded positive endpoints and actual coprime additive equations.

Two `fail_if_success exact ...` probes reject direct use of the partially applied normal-form theorem and a loaded split at the chart-nonempty goal. The containing example closes only with explicit hrec. These are type-contract checks, not a universal impossibility or independence proof. The existing root-ne-innerRoot theorem is also applied with a supplied route/carrier equality.

SHA256, paths relative to working directory:

```text
515d710207ce0d1c14eea83a530f0e0d0f8d50dd6b8841392f7523d53778abad  DkMath/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean
17f4f7c09d007b8cf3b9f3fd8201fc278768f31e5057073b1f62aea9a2c5d836  DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean
```

Raw logs `logs/__017-*.txt` are temporary and ignored. Source inspection is distinct from the focused build and executable probes. No new constructive source→chart implication, prime search or FLT7 result is claimed.
