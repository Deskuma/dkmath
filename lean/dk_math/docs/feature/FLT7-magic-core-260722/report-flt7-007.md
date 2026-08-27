# FLT7-007 implementation report

## Outcome

Outcome A. The exact ramifier power split and quadratic terminal residual
packet are complete. The residual norm is exactly the seventh power supplied
by the natural split; no element-level seventh-power claim is made.

## Files changed

- `DkMath/FLT/Seven/SevenAdicPowerSplit.lean`
- `DkMath/FLT/Seven/QuadraticResidualPacket.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenAdicPowerSplit.lean`
- `DkMathTest/FLT/SevenQuadraticResidualPacket.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-007.md`

## Public surface

Natural stripping and split:

- `sevenAdicPacket_residual_not_fortyNine_dvd`
- `sevenAdicPacket_seven_not_dvd_strippedResidual`
- `sevenAdicPacket_coprime_div_seven`
- `sevenAdicPacket_coprime_scaledGap_residual`
- `sevenAdicPacket_normalized_product`
- `SevenAdicPowerSplit`
- `SevenAdicPowerSplit.seven_not_dvd_b`
- `nonempty_sevenAdicPowerSplit_of_packet`
- `sevenAdicPowerSplit_of_packet`
- `sevenAdicPowerSplit_of_counterexample`

Quadratic residual:

- `SevenQuadraticResidualPacket`
- `nonempty_sevenQuadraticResidualPacket_of_powerSplit`
- `sevenQuadraticResidualPacket_of_powerSplit`
- `sevenQuadraticResidualPacket_of_counterexample`
- `SevenQuadraticResidualPacket.norm_is_seventh_power`
- `SevenQuadraticResidualPacket.norm_positive`

## Exact stripping architecture

For `c=(z-y)/7`, `r=GN/7`, and `d=x/7`, packet divisibility reconstructs

```text
z-y = 7c,   GN = 7r,   x = 7d.
```

The exact gcd field and `Nat.coprime_div_gcd_div_gcd` give `Coprime c r`.
Valuation one rules out `49∣GN`, hence `7∤r`; this permits the stronger
`Coprime (7^2*c) r`. Rewriting the three reconstruction identities into the
body equation proves

```text
(7^2*c)r = (7d)^7.
```

Splitting this coprime product gives `7^2*c=A^7` and `r=b^7`. Primality forces
`A=7a`; exact cancellation then yields `c=7^5*a^7`. Reconstruction and
injectivity of the seventh-power map establish

```text
z-y = 7^6*a^7,
GN 7 (z-y) y = 7*b^7,
x = 7*a*b.
```

Positivity follows from the positive gap and GN factor. Coprimality of the
stripped cores descends to `Coprime a b`, while no-`49` gives `7∤b`.

## Quadratic terminal residual

The primitive gap branch supplies a unique peeled `sevenAxis` layer:

```text
cyclotomicSevenToTraceOne z y = sevenAxis * residualCore.
```

The existing terminal-core API records nonzeroness, axis terminality,
nondivisibility of its norm by seven, and
`cyclotomicSeven z y = 7 * norm residualCore`. The natural bridge identifies
the same cyclotomic value with `GN = 7*b^7`; cancellation of the nonzero
integer factor `7` proves exactly

```text
norm residualCore = b^7.
```

This is only a norm statement. The packet deliberately does not assert that
`residualCore` is a unit times a seventh power.

## Verification

The following checks passed:

- `lake build DkMath.FLT.Seven.SevenAdicPowerSplit`
- `lake build DkMath.FLT.Seven.QuadraticResidualPacket`
- `lake build DkMath.FLT.Seven`
- `lake env lean DkMathTest/FLT/SevenAdicPowerSplit.lean`
- `lake env lean DkMathTest/FLT/SevenQuadraticResidualPacket.lean`
- `lake build DkMath.FLT`
- forbidden-token scan over the new modules and focused tests
- `git diff --check`

The tests use abstract packets only. Every audited theorem reports exactly the
standard Lean/Mathlib axiom set `[propext, Classical.choice, Quot.sound]`.
There are no project-specific axioms, and the checkpoint contains no
`native_decide`, `admit`, or `sorry`.

## Recommended FLT7-008 boundary

Investigate the arithmetic needed to turn a terminal element of
`TraceOneInt (-2)` with seventh-power norm into an element-level normal form.
Keep three routes separate: a direct Euclidean-domain construction for the
discriminant `-7` order; coprime-conjugate extraction without a global UFD
instance; and finite unit classes modulo seventh powers. Do not start descent
until the factorization and unit-sector APIs are explicit.
