# FLT7-006 implementation report

## Outcome

Outcome A.  The primitive counterexample packet, exact body factorization,
common-divisor branch control, away seventh-power split, ramified valuation
shape, fixed-thickness consequence, packet, and route classification are all
complete.

## Files changed

- `DkMath/FLT/Seven/Basic.lean`
- `DkMath/FLT/Seven/CounterexampleRouting.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenCounterexampleRouting.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-006.md`

## Definitions and structures

- `Fermat7Equation`
- `CounterexamplePack`
- `Body7`
- `SevenAdicCounterexamplePacket`
- `CounterexampleRoute`

## Theorem surface

Basic and primitive endpoint layer:

- `seventh_sub_eq_of_add_eq`
- `right_lt_of_fermat7Equation`
- `gap_pos_of_fermat7Equation`
- `coprime_y_z_of_counterexamplePack`
- `coprime_gap_y_of_counterexamplePack`

Body and common-divisor layer:

- `body7_eq_seventh_power_of_counterexample`
- `GN_seven_pos_of_counterexample`
- `body7_ne_zero_of_counterexample`
- `GN_seven_eq_gap_mul_add_seven_mul_y_pow_six`
- `gcd_gap_GN_seven_dvd_seven`
- `gcd_gap_GN_seven_eq_one_of_not_seven_dvd`
- `gcd_gap_GN_seven_eq_seven_of_seven_dvd`
- `branchAway_coprime_gap_GN_seven`
- `branchRamified_gcd_gap_GN_seven`

Routing and valuation layer:

- `seventh_power_factor_split`
- `branchAway_seventh_power_factor_split`
- `not_seven_dvd_y_of_counterexample_of_seven_dvd_gap`
- `seven_dvd_x_of_counterexample_of_seven_dvd_gap`
- `padicValNat_GN_seven_eq_one_of_counterexample`
- `padicValNat_carrier_shape_of_mul_eq_seventh`
- `padicValNat_gap_shape_of_counterexample`
- `seven_pow_six_dvd_gap_of_counterexample`
- `sevenAdicCounterexamplePacket_of_branch`
- `counterexampleRoute_of_pack`

## Primitive endpoint coprimality

If a prime divided both `y` and `z`, the Fermat equation would make it divide
`x^7`, hence `x`, contradicting the recorded `Coprime x y`.  This proves
`Coprime y z`.  Natural subtraction with `y≤z` then transfers it to
`Coprime (z-y) y`.

## Exact body and common-divisor support

The generic additive GN identity at degree seven gives

```text
(z-y) * GN 7 (z-y) y = x^7.
```

The local exceptional-term decomposition is

```text
GN 7 g y = g * (...) + 7*y^6.
```

Thus `d=gcd(g,GN)` divides `7*y^6`.  Since `d∣g` and `g` is coprime to `y`,
`d` is coprime to `y^6`; cancellation removes the endpoint factor and proves
`d∣7`.  Away from seven, `d=1`.  On `7∣g`, FLT7-005 supplies `7∣GN` using the
endpoint convention `(g+y,y)`, so `d=7` exactly.

## Two routing branches

Away from seven, the gap and GN factor are coprime.  Mathlib's
`exists_eq_pow_of_mul_eq_pow` splits their seventh-power product into
individual seventh powers.  This is a normal form, not a contradiction.

On the ramified branch, primitive coprimality gives `7∤y`; the body equation
gives `7∣x`; and FLT7-005 gives

```text
padicValNat 7 (GN 7 (z-y) y) = 1.
```

Valuation multiplicativity and the seventh power identity yield

```text
padicValNat 7 (z-y) + 1 = 7 * padicValNat 7 x,
```

so the gap valuation has shape `6+7m`.  In particular `7^6∣z-y`.

## Packet and summit route

`SevenAdicCounterexamplePacket` records the factor equation, exact gcd,
endpoint exclusions, residual valuation one, gap valuation shape, and the
`7^6` fixed-thickness consequence.  `counterexampleRoute_of_pack` decides only
whether `7` divides the gap and returns either the away power split or this
ramified packet.  Neither constructor is declared impossible.

## Scope preserved

No FLT7 no-solution theorem, contradiction, descent, general LTE,
ideal/PID/UFD/Euclidean/class-number theory, general prime abstraction,
primitive-prime provider, or FLT3/FLT5 change was added.

## Verification and axiom audit

The following checks passed:

- `lake build DkMath.FLT.Seven`
- `lake env lean DkMathTest/FLT/SevenCounterexampleRouting.lean`
- `lake build DkMath.FLT`
- forbidden-token scan over the FLT7 implementation and routing test
- `git diff --check`

The abstract wiring test exercises the body identity, away split, ramified
packet construction, fixed-thickness extraction, and both eliminator branches
of `CounterexampleRoute`; it does not postulate a concrete counterexample.

Every audited summit theorem reports exactly the standard Lean/Mathlib axiom
set `[propext, Classical.choice, Quot.sound]`.  There are no project-specific
axioms, and the implementation contains no `native_decide`, `admit`, or
`sorry`.

## Recommended FLT7-007 boundary

Strip the ramifier in `SevenAdicCounterexamplePacket` and derive a coprime
seventh-power factor pair, or design the quadratic-order factorization consumed
by both routes.  Do not claim descent until the residual coordinate packet and
its strictly decreasing measure are explicit.
