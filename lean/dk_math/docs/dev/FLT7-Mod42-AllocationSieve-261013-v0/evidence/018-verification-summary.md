# 018 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した tool 出力の要約。第三者の独立再検証ではない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger` | exit 0; 9087 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean` (final corrected run) | exit 0 |
| new Lean forbidden construct scan | rg exit 1; no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Initial calibration and initial test each exited1; corrected runs exited0. Calibration needed a change to normalize the K alias; test needed replacement of absent Nat.mul_pos_iff. No mathematical hypotheses changed.

Build excerpt:

```text
Built DkMath.FLT.Seven.SevenRamifiedFusionSourcePrimeValuationLedger (5.8s)
Build completed successfully (9087 jobs).
```

All3 exports in namespace `DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport` were explicitly audited with `#print axioms`:

- `internalDepthFour_source_outerRoots_coprime`
- `internalDepthFour_source_prime_valuation_balance`
- `internalDepthFour_source_prime_exclusive_valuation`

Each reported `[propext, Classical.choice, Quot.sound]`. The test declaration `DkMathTest.FLT.Seven.productOnly_nonexclusive_countermodel` was also audited and reported the same list. No sorryAx.

Source inputs: actual complementary-root existential; source core positivity; canonical.vertical_coprime_compensation_residual; compensationCore=C^7. Mathlib valuation additivity uses explicit prime instance and nonzero factors. Tests verify factorization readout, positivity, exclusive branches, previous support consequence and zero convention. The generic M=4,N=1,V=C=2 countermodel is not a source-packet counterexample.

SHA256, relative to working directory:

```text
668821fc4b7643d8eaa90e5676ee1c802fc287c4e409690d3b2249b4ea63dd41  DkMath/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean
a50550a3ed743da2432cbfa1efba4139fa32c236cab91acfaca40e0a272caad8  DkMathTest/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean
```

Raw logs `logs/__018-*.txt` are temporary/ignored. No Python mathematical precheck, new modulus search or additive endpoint search was executed. The new readout is a consequence of existing source facts, not an independent core bound or reconstruction-existence proof.
