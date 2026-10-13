# 014 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した Lean/tool 出力の要約。第三者の独立再検証ではない。数学的 Python precheck は実行していない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership` | exit 0 |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean` | exit 0 |
| new-file forbidden construct scan | rg exit 1, no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Focused build ending:

```text
Built DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership (5.0s)
Build completed successfully (9091 jobs).
```

Each of the following declarations was audited with `#print axioms` and depends only on `[propext, Classical.choice, Quot.sound]`:

- `DkMath.FLT.Seven.eligible_primitive_divisor_smallCoefficient_prime_pow`
- `DkMath.FLT.Seven.sixthPowerSieved_three_thirteen_pow_excluded`
- `DkMath.FLT.Seven.threeThirteenPowerCore_injective`
- `DkMath.FLT.Seven.sixthPowerSieved_three_thirteen_power_family_excluded`
- `DkMathTest.FLT.Seven.coefficientBound_countermodel`

No sorryAx. The test checks the n=12 whole-core regression by applying the positive-exponent theorem, not by finite endpoint enumeration. The countermodel is kernel-checked `decide`; the ownership and family results use generic arithmetic proofs and existing consumers. The gate 013 mod13 proof is reused as an imported dependency.

SHA256, paths relative to working directory:

```text
47ce3bd11f3a76530db8ab3090e18f581c19b5cb39280af58307481ea2b9087b  DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean
0811f9c12fc2116cac8f3185dc26fbce698df03fde145a8cf5057f9cc2e1fc29  DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean
```

Raw temporary logs use ignored `logs/__014-*.txt` filenames. No packet or unconditional FLT7 claim is made.
