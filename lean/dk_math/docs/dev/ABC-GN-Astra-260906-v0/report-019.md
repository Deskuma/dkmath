# LUNA-019 — paired squareful / square-cube ledger

## Scope and files

This checkpoint consumes the LUNA-018 paired orientation ledger and freezes
the squareful and canonical square-cube structure of both repeated
coordinates.  It introduces no relative-height, counting, density, or ABC
closure theorem.

Changed files:

- `DkMath/ABC/GNExcessCubicPairedSquareful.lean`
- `DkMath/ABC.lean` (public import immediately after the paired orientation module)
- `README.md`, `ROADMAP.md`, `validation-019.txt`, and this report.

## Squareful and square-cube coordinates

The generic theorem `repeatedPrimePowerPart_squarefull` is a direct consumer of
the existing `prime_sq_dvd_repeatedPrimePowerPart` theorem.  The forward and
swap repeated parts therefore satisfy

```text
squarefull MF
squarefull MG
```

and both are positive.  The canonical LUNA-014 quotient API gives the paired
coordinates

```text
MF = uF^2 * rF^3       MG = uG^2 * rG^3
rF = oddPart MF       rG = oddPart MG
uF = GNExcessCubicSquarefulQuotient MF
uG = GNExcessCubicSquarefulQuotient MG
```

with `Squarefree rF`, `Squarefree rG`, and positivity of all four coordinates.
`GNCubicPairedRepeatedParts_squareCube_packet` exposes this exact packet.

The repeated product is squarefull and has the exact identity

```text
MF*MG = (uF*uG)^2 * (rF*rG)^3.
```

The paired coprimality from LUNA-018 transfers to `Coprime rF rG` and
`Coprime uF uG`; consequently `Squarefree (rF*rG)` is proved.  The optional
oddPart/evenPart multiplicativity theorem was not added because the explicit
square-cube identity already supplies the required canonical coordinate form.

## Support and quartic consumers

Prime divisors of either repeated coordinate are `1 mod 3`, and the product
consumer `GNCubicPairedRepeatedProduct_prime_mod_three_eq_one` preserves this
support statement.  The forward `a = 0` edge is discharged by the square
divisibility of the repeated prime-power part together with its divisibility
into `GN 3 0 1 = 3`.

`GNCubicPairedRepeatedProduct_squareful_packet` combines squarefullness, the
square-cube identity, squarefreeness of the combined cube-core, and the
LUNA-018 quartic divisibility

```text
MF*MG ∣ 3*(a+1)^4 + a^2.
```

For every prime `q` dividing `MF*MG`, the module records `q^2 ∣ MF*MG` and
therefore `q^2 ∣ 3*(a+1)^4 + a^2`.  This is only local square divisibility;
no rarity, density, or Hensel-decay conclusion is drawn.

## Sector packets and regression boundary

`GNCubicPaired_offSeven_squareCube_packet` combines the canonical square-cube
coordinates with all four LUNA-018 off-seven cross-coprimality facts.
`GNCubicPaired_sevenSector_squareful_packet` records, for `a % 7 = 1`, the
orientation gcd `7`, the non-simultaneous `49` divisibility boundary, repeated
part coprimality, and squarefullness of both repeated parts.  It does not say
which orientation carries repeated `7`-depth.

The imported regression
`exists_arbitrarily_large_coprime_cubic_repeated_parts` remains explicit:
squarefullness, coprimality, and exact square-cube coordinates do not imply
that either repeated part is small relative to `a`.

## Verification and trust boundary

```text
lake build DkMath.ABC.GNExcessCubicPairedSquareful  PASS
lake build DkMath.ABC                              PASS
```

Changed production sources contain no new `sorry`, `admit`, `axiom`,
`abc_main_axiom`, or `native_decide`.  Audited principal declarations remain
within `propext`, `Classical.choice`, and `Quot.sound`.

The remaining frontier is paired relative-height exclusion, shell counts,
squarefull asymptotics, Hensel/Pell rarity, density, and ABC quality coupling.
No theorem here claims `MF*MG ≤ (a+1)^2`, that one repeated part is small, or
that square divisibility of the quartic has any density consequence.
