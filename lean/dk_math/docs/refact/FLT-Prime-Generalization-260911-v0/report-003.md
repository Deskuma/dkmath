# FLT prime-generalization Phase 3 — Seven adic front-half specialization

## Scope and outcome

This report implements the bounded refactor in `instruction-003.md`. The
public FLT7 `SevenAdicPowerSplit` API remains unchanged, but its existence
constructor now comes from the generic odd-prime `PrimeAdicPowerSplit` kernel
specialized at `p = 7`. The old Seven-specific quadratic, real-cubic,
cyclotomic, and downstream FUSION layers were not generalized.

The result is Outcome A: the ramified power split is rebuilt from the generic
prime kernel without weakening its public output, and the focused downstream
builds remain green.

## Part A — production bridge

`DkMath.FLT.Seven.SevenAdicPowerSplit` now defines:

```lean
SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
```

with target
`PrimeAdicFactorPacket 7 (z - y) y x`.

The bridge is classified `PGEN-SPECIALIZATION`. It uses only the existing
ramified packet's branch/factor data and existing Seven consequences:

- positivity of `z - y` and `x` from the `CounterexamplePack`;
- `Nat.Coprime (z - y) y` from the existing counterexample routing lemma;
- `7 ∣ z - y` from `seven_dvd_gap`;
- the existing body factorization from `factor_eq`.

The stored residual valuation, gap valuation shape, `7^6` divisibility, and
the separate divisibility fields are not required by the generic input
constructor; the generic kernel derives the relevant residual and carrier
facts.

## Part B — generic reconstruction of the public Seven split

`nonempty_sevenAdicPowerSplit_of_packet` now calls

```lean
DkMath.FLT.Prime.nonempty_primeAdicPowerSplit_of_packet
  p.toPrimeAdicFactorPacket
```

and repackages the returned witnesses into the existing
`SevenAdicPowerSplit` structure. The legacy output remains exactly in the
Seven/GN presentation:

```text
z - y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
x = 7 * a * b
```

The hand-built constructor chain through stripped `c`, `r`, `d`, the manual
coprimality/product proof, the seventh-power factor split, and the explicit
`7^6` carrier extraction is no longer used. The current tracked diff removes
147 old proof lines and replaces them with 57 bridge/wrapper lines across the
refactored production and test files.

## Part C — helper classification and compatibility surface

The following helpers now use the promoted generic API directly or through a
thin legacy-shape wrapper:

| Declaration family | Classification | Generic source |
|---|---|---|
| `gcd_gap_GN_seven_dvd_seven` | `PGEN-SPECIALIZATION` | `gcd_GN_eq_gcd_of_one_le` |
| `gcd_gap_GN_seven_eq_one_of_not_seven_dvd` | `PGEN-SPECIALIZATION` | `gcd_GN_prime_eq_one_of_not_dvd` |
| `gcd_gap_GN_seven_eq_seven_of_seven_dvd` | `PGEN-SPECIALIZATION` | `gcd_GN_prime_eq_prime_of_dvd` |
| `seventh_power_factor_split` | `PGEN-SPECIALIZATION` | `DkMath.Lib.NumberTheory.power_factor_split` |
| `padicValNat_GN_seven_eq_one_of_counterexample` | `PGEN-SPECIALIZATION` | `padicValNat_GN_prime_eq_one_of_dvd_gap` |
| `padicValNat_carrier_shape_of_mul_eq_seventh` | `PGEN-SPECIALIZATION` | `padicValNat_carrier_shape_of_mul_eq_prime` |
| `seven_pow_six_dvd_gap_of_counterexample` | `PGEN-SPECIALIZATION` | `prime_pow_sub_one_dvd_carrier` |
| `sevenAdicPacket_residual_not_fortyNine_dvd` | `PGEN-SPECIALIZATION` | `PrimeAdicFactorPacket.residual_not_prime_sq` |
| `sevenAdicPacket_seven_not_dvd_strippedResidual` | `PGEN-SPECIALIZATION` | generic residual divisibility/no-square facts |
| `sevenAdicPacket_coprime_div_seven` | `PGEN-SPECIALIZATION` | `PrimeAdicFactorPacket.gcd_gap_residual` |
| `sevenAdicPacket_coprime_scaledGap_residual` | `PGEN-COMPAT` | generic residual unit fact plus legacy Nat division shape |
| `sevenAdicPacket_normalized_product` | `PGEN-COMPAT` | generic packet factorization plus legacy Nat division shape |
| `padicValNat_gap_shape_of_counterexample` | `PGEN-COMPAT` | retained Seven-shaped wrapper around the generic carrier theorem |

The old theorem names and the `SevenAdicPowerSplit` fields are intentionally
retained because production modules and tests still consume the legacy
Seven-specific factor-split helper, and downstream source compatibility is
part of this phase. The production Seven constructor no longer depends on the
old manual helper chain.

`CounterexampleRouting` itself remains a Seven-specific route packet. Its
`Body7`, Fermat-7 counterexample, away/ramified branch, and public packet
construction are `P7-STRUCTURAL`; only the duplicated generic arithmetic
inside it was collapsed.

## Part D — first Seven-specific algebraic frontier

`SevenAdicPowerSplit` is now the `PGEN-SPECIALIZATION FRONTIER OUTPUT`.

The immediate downstream module
`DkMath.FLT.Seven.QuadraticResidualPacket` is confirmed as the
`P7-FIRST-ALGEBRAIC-FRONTIER`. Its first nontrivial construction requires
the genuinely Seven-specific ingredients:

- `TraceOneInt (-2)`;
- `sevenAxis`;
- `cyclotomicSevenToTraceOne`;
- `exists_cyclotomicSeven_terminal_core`.

That packet is therefore not generalized in this phase. Before this frontier,
the remaining Seven-specific material is the exponent-seven counterexample
route, legacy `GN`/`Body7` presentation, ramified branch packet, and the
compatibility wrappers listed above.

## Verification

The required focused builds passed sequentially:

```text
lake build DkMath.FLT.Prime.AdicPowerSplit                 # 8662 jobs
lake build DkMath.FLT.Seven.CounterexampleRouting          # 8678 jobs
lake build DkMath.FLT.Seven.SevenAdicPowerSplit             # 8679 jobs
lake build DkMath.FLT.Seven.QuadraticResidualPacket        # 8680 jobs
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility # 8680 jobs
lake build DkMath.FLT.Seven                                 # 8810 jobs
lake build DkMathTest.FLT.SevenAdicPowerSplit               # 8811 jobs
```

The existing routing regression also passed:

```text
lake build DkMathTest.FLT.SevenCounterexampleRouting         # 8811 jobs
```

The ordinary FLT7 facade remains free of the separated theta-jet existence
branch. Its dependency replay contains the generic Prime kernel and the
structural Seven modules, but not
`SevenRealCubicThetaSeventhPower` or `SevenRamifiedThetaJetLifting`.

`git diff --check` passed.

## Axiom audit

The Seven adic split regression prints axioms for:

```text
SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
nonempty_sevenAdicPowerSplit_of_packet
sevenAdicPowerSplit_of_packet
sevenAdicPowerSplit_of_counterexample
SevenQuadraticResidualPacket.norm_is_seventh_power
```

The routing and generic compatibility audits also passed. Checked
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` was reported. Source scans of the changed production and test
files found no `sorry` or `axiom` construct.

No FLT7 contradiction, general FLT theorem, or generalization of the
discriminant-`-7` algebraic layer is claimed.
