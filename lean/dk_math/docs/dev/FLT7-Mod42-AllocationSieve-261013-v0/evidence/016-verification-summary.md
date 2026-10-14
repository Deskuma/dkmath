# 016 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した tool 出力の要約。独立した第三者再検証ではない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport` | exit 0; 9090 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean` | exit 0 |
| new-file forbidden construct scan | rg exit 1, no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Build excerpt:

```text
Built DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport (6.5s)
Build completed successfully (9090 jobs).
```

Explicit `#print axioms` results, all names in `DkMath.FLT.Seven` unless test-qualified:

| Declaration | Axioms |
|---|---|
| `zmod_seventh_power_injective` | propext, Classical.choice, Quot.sound |
| `centeredSevenSextic_cast_difference` | propext, Quot.sound |
| `centeredSevenSextic_not_dvd_of_seven_power_permutation` | propext, Classical.choice, Quot.sound |
| `nestedAllocation_excluded_of_permutation_prime_support` | propext, Classical.choice, Quot.sound |
| `sixthPowerSieved_smallCoefficient_permutation_prime_excluded` | propext, Classical.choice, Quot.sound |
| `DkMathTest.FLT.Seven.twentyNine_countermodel` | propext, Classical.choice, Quot.sound |
| `DkMathTest.FLT.Seven.two_countermodel` | propext, Classical.choice, Quot.sound |
| `DkMathTest.FLT.Seven.seven_gap_support_diagnostic` | propext, Classical.choice, Quot.sound |

No sorryAx. The general proof uses the group theorem `Nat.Coprime.pow_left_bijective` and `ZMod.card_units`, treats zero separately, and uses a ring identity followed by nonzero-product contradiction. Countermodels and concrete prime assumptions use kernel-checked decide. Instruction BigInt tables are not proof dependencies; no Python mathematical precheck was executed.

SHA256, paths relative to working directory:

```text
45de712fc453d175aaa8acf5707ecbeff0c53d046f714e5fdfac0d027c7dd8ec  DkMath/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean
8089507771de91284a961307f076f04572ffdcf1779680509b556a0b0f1b7baf  DkMathTest/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean
```

Temporary logs use ignored `logs/__016-*.txt` names. Scope is abstract receiver/sieve exclusion under explicit sufficient prime conditions; no source realization or FLT7 claim.
