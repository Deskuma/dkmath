# LUNA-018 — paired-orientation exact arithmetic ledger

## Scope and files

This checkpoint freezes the one-parameter pair
`F(a) = GN 3 a 1 = a^2 + 3*a + 3` and
`G(a) = GN 3 1 a = 3*a^2 + 3*a + 1`.
It isolates ordinary common support at `7` and keeps the two non-exceptional
repeated parts coprime.  No relative-height or ABC closure statement is added.

Changed files:

- `DkMath/ABC/GNExcessCubicPairedOrientation.lean`
- `DkMath/ABC.lean` (public import after the three-sector incidence module)
- `README.md`, `ROADMAP.md`, `validation-018.txt`, and this report.

## Frozen paired ledger

The module exposes minimal value and repeated-part wrappers:

```text
GNCubicForwardValue a = GN 3 a 1
GNCubicSwapValue a = GN 3 1 a
GNCubicForwardRepeatedPart a = GNNonExceptionalRepeatedPart 3 a 1
GNCubicSwapRepeatedPart a = GNNonExceptionalRepeatedPart 3 1 a
```

The explicit quadratic values are kernel-checked.  The swap orientation has no
factor `3`, so its non-exceptional repeated part is exactly
`repeatedPrimePowerPart (GN 3 1 a)`.  The new swap complement is squarefree,
coprime to the swap repeated part, and satisfies the exact product identity.

For positive `a`, `GNCubicPairedRepeatedComplement_packet` records

```text
MF*SF = F(a)       MG*SG = G(a)
Squarefree SF      Squarefree SG
Coprime MF SF     Coprime MG SG
Coprime MF MG
```

The ordinary orientation gcd is sharpened from `14` to `7`.  Exact modular
arithmetic proves

```text
7 ∣ F(a) ∧ 7 ∣ G(a)  ↔  a % 7 = 1
gcd(F(a),G(a)) = 7    ↔  a % 7 = 1
gcd(F(a),G(a)) = 1    ↔  a % 7 ≠ 1
```

The prime-overlap theorem says that a prime dividing both orientations is
necessarily `7`, with `a % 7 = 1`.

## Exact couplings and sectors

The paired complement product and integer linear difference are frozen:

```text
(MF*SF)*(MG*SG) = 3*(a+1)^4 + a^2
MF*MG ∣ 3*(a+1)^4 + a^2
3*(MF*SF) - (MG*SG) = 6*a + 8       (over ℤ)
```

`gcd_dvd_seven_of_dvd_cubic_orientations` is instantiated by
`GNCubicPaired_cross_gcd_packet` for `gcd MF SG`, `gcd SF MG`, and `gcd SF SG`.
Together with the repeated-part coprimality, the
`GNCubicPaired_offSeven_cross_coprime_packet` proves all four factor-coordinate
coprimalities when `a % 7 ≠ 1`.

The `GNCubicPaired_sevenSector_packet` records only the safe boundary facts:
the orientation gcd is `7`, both orientations are divisible by `7`, they are
not both divisible by `49`, and `MF` and `MG` are coprime.  It deliberately
makes no claim about which orientation carries repeated `7`-depth.

The optional squarefull strengthening is not added; the exact product identity
and repeated-product divisibility are the recorded coupling facts.

The imported regression
`exists_arbitrarily_large_coprime_cubic_repeated_parts` remains visible: both
repeated parts can be arbitrarily large in absolute size while staying
coprime.  No size-relative inference is made.

## Verification and trust boundary

Focused and public-aggregator builds pass:

```text
lake build DkMath.ABC.GNExcessCubicPairedOrientation  PASS
lake build DkMath.ABC                                   PASS
```

The changed production sources introduce no `sorry`, `admit`, new `axiom`,
`abc_main_axiom`, or `native_decide`.  Audited principal declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

The remaining research frontier is paired relative-height exclusion, bounds
on either repeated part, shell counts, Hensel/Pell rarity, density, and ABC
quality coupling.  Coprime repeated parts do not imply that either orientation
is small, and the unique ordinary overlap prime does not bound repeated depth.
The ASTRA-007 paired relative-height numerical signal remains unproved.  These
are outside LUNA-018.
