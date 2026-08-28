# PUU-L004: Unit Intersection Trichotomy / Commensurability Closure

## Result

PUU-L004 is implemented in
`DkMath.NumberTheory.PrimorialUniverse.UnitIntersectionClassification` and
exported through the existing PrimorialUniverse facade.

## Definitions and normalization

- `UnitsCommensurable u₁ u₂` means that positive coprime natural coordinates
  synchronize the two positive units.
- `HasPositiveCommonLatticePoint u₁ u₂` means that both units represent one
  real point using positive natural coordinates.
- `UnitsPartiallySynchronize` means commensurable but unequal unit values.

For a positive common pair `(m,n)`, the implementation sets

```text
g = gcd(m,n), a = m/g, b = n/g.
```

Mathlib's gcd normalization gives positive `a,b` and `Nat.Coprime a b`.
Cancelling the positive real factor `g` in
`m*u₁ = n*u₂` gives `a*u₁ = b*u₂`, so every positive intersection produces
the canonical coprime synchronization required by PUU-L003.

## Main equivalence

The theorem `hasPositiveCommonLatticePoint_iff_unitsCommensurable` proves:

```text
positive common lattice point exists
  ↔
positive integer synchronization exists.
```

The theorem `noPositiveCommonLatticePoint_iff_not_unitsCommensurable` gives the
negated form.  Zero is intentionally not part of this classification.

## Three cases

`unitIntersection_trichotomy` exposes the following exhaustive disjunction:

1. `u₁.val = u₂.val`: complete synchronization; every natural coordinate
   matches itself, supplied by `equalUnits_allCoordinates_common`.
2. `UnitsPartiallySynchronize u₁ u₂`: positive common points exist, but no
   positive same-coordinate common point exists.
3. `¬ UnitsCommensurable u₁ u₂`: no positive common lattice point exists.

The partial case is not claimed to be finite.  PUU-L003 still supplies the
infinite fiber `(a*t,b*t)` for every natural `t`.

The optional ratio bridge was not attempted: this checkpoint remains in the
integer commensurability language and does not classify rational versus
irrational real ratios.

## Regression and boundary

The existing units `3` and `2` with synchronization `2*3 = 3*2` are recorded
as a partial synchronization regression.  Prime/composite labels remain
relative to natural coordinates; no absolute real point receives such a
label.

This checkpoint does not introduce arbitrary field or lattice abstractions,
three-or-more-unit synchronization, lcm/primorial products, reduced-residue
wheels, reflection/lift rules, PowerSwap, GN/CosmicFormula, Legendre, square
anchors, analytic sieve, PNT, or RH.

## Verification

The focused classification module, public facade, and top-level `DkMath`
target were built successfully.  `git diff --check` and prohibited-source
scans were run.  No commit, push, merge, or CI action was performed.
