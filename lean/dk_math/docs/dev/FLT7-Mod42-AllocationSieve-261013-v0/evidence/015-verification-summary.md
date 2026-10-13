# 015 verification summary

2026-10-14。Provenance: Codex が現在の checkout で実行した tool 出力の要約。第三者の独立再検証ではない。数学的 Python precheck は実行していない。

Working directory: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。

| Command / check | Actual status |
|---|---|
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport` | exit 0; 9093 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean` | exit 0 |
| forbidden constructs scan of new Lean files | rg exit 1, no matches |
| `git diff --check` | exit 0 |
| new-file whitespace check | PASS |

Build excerpt:

```text
Built DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport (6.2s)
Build completed successfully (9093 jobs).
```

`#print axioms` was run for each of the following. All reported `[propext, Classical.choice, Quot.sound]`; none reported sorryAx.

- `DkMath.FLT.Seven.eligible_primitive_divisor_smallCoefficient_prime_not_dvd`
- `DkMath.FLT.Seven.eligible_smallCoefficient_prime_in_complement`
- `DkMath.FLT.Seven.sixthPowerSieved_smallCoefficient_thirteen_pow_excluded`
- `DkMathTest.FLT.Seven.priorPassage_and_coreExclusion`
- `DkMathTest.FLT.Seven.coefficientDivisibility_countermodel`
- `DkMathTest.FLT.Seven.coefficientThirteen_eligible_support`

The main results use generic prime/quotient arithmetic and gate 013's checked consumer. Test arithmetic and the limited divisibility countermodel use kernel-checked decide. The c=13,n=2,r=1 test derives the support pair via the generic bridge from concrete eligibility guards. All coefficient regressions quantify over arbitrary positive exponents.

SHA256, paths relative to working directory:

```text
9e95c71b9985a716c9c68362ea8771c1f30182f6783c857ea40a7e330feb930f  DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean
61977f588c7288b6e06e3d48a18dd8cf5184c64b485a270050c58dda98c3680b  DkMathTest/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean
```

Temporary logs `logs/__015-*.txt` are confirmed ignored. No actual source-core realization, packet result or FLT7 claim is made.
