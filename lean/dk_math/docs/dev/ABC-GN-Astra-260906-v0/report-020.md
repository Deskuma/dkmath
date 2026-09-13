# LUNA-020 — seven-depth state normalization

## Scope and files

This checkpoint normalizes the paired cubic orientation sector modulo `49`.
It consumes the LUNA-018 orientation ledger and LUNA-019 squareful ledger and
adds only local divisibility, residue, packet, and gcd facts.  No counting,
density, relative-height, or ABC closure theorem is introduced.

Changed files:

- `DkMath/ABC/GNExcessCubicSevenDepth.lean`
- `DkMath/ABC.lean` (public import immediately after the squareful module)
- `README.md`, `ROADMAP.md`, `validation-020.txt`, and this report.

## Generic bridge and residue classification

The new generic theorem
`prime_dvd_repeatedPrimePowerPart_iff_sq_dvd` proves, for prime `q` and
nonzero `n`,

```text
q ∣ repeatedPrimePowerPart n  ↔  q^2 ∣ n.
```

The proof uses the existing square-divisibility and factorization support
APIs; it adds no valuation machinery.  Its cubic consumers give

```text
7 ∣ MF(a) ↔ 49 ∣ F(a)
7 ∣ MG(a) ↔ 49 ∣ G(a).
```

For `a % 7 = 1`, the algebraic lift is proved with `a = 7*(a/7)+1`:

```text
F(a) = 7 * (7*k^2 + 5*k + 1)
G(a) = 7 * (21*k^2 + 9*k + 1),  k = a/7.
```

Exact modular arithmetic then establishes

```text
49 ∣ F(a) ↔ a % 49 = 29
49 ∣ G(a) ↔ a % 49 = 22.
```

The two residues are disjoint, and the existing cubic prime-square obstruction
is exposed as `not_fortyNine_dvd_both_cubic_orientations`.

## Three state packets

`GNCubicPaired_forwardSevenDeep_packet` records the forward-deep state
(`a % 49 = 29`), including `7 ∣ MF`, `¬7 ∣ MG`, `¬7 ∣ SF`, and `7 ∣ SG`.
`GNCubicPaired_swapSevenDeep_packet` records the symmetric swap-deep state
(`a % 49 = 22`).  `GNCubicPaired_shallowSeven_packet` records the remaining
`a % 7 = 1` state, with both repeated parts avoiding `7` and both complements
carrying `7`.

The cross-gcd divisibility ledger is sharpened to exact values in
`GNCubicPaired_forwardSevenDeep_crossGcd_packet`,
`GNCubicPaired_swapSevenDeep_crossGcd_packet`, and
`GNCubicPaired_shallowSeven_crossGcd_packet`.  The repeated-product consumers
`seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState` and
`fortyNine_dvd_GNCubicPairedRepeatedProduct_iff_deepState` identify exactly the
two deep residues, and `GNCubicPaired_sevenDepth_cases` gives the three-way
residue trichotomy.

No theorem bounds the depth above two: deeper `7`-adic valuation remains
outside this checkpoint.  No residue count, density estimate, relative-height
bound, or ABC conclusion is claimed.

## Verification and trust boundary

```text
lake build DkMath.ABC.GNExcessCubicSevenDepth  PASS
lake build DkMath.ABC                              PASS
```

Changed production sources contain no new `sorry`, `admit`, `axiom`,
`abc_main_axiom`, or `native_decide`.  The principal declaration audit remains
within `propext`, `Classical.choice`, and `Quot.sound`.

The remaining frontier is the same as before: paired relative-height
exclusion, shell counts, squareful asymptotics, Hensel/Pell rarity, density,
and ABC quality coupling.  The separate H2 cubic `3/8` boundary-weight
candidate is not used or claimed here; it remains a future production task.
