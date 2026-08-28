# PUU-L003: Coprime Common-Lattice Fiber

## Result

PUU-L003 is implemented in
`DkMath.NumberTheory.PrimorialUniverse.CommonLattice` and exported by the
existing `DkMath.NumberTheory.PrimorialUniverse` facade.

## Public API

- `UnitSynchronizesBy u₁ u₂ a b` records positive coprime coordinates with
  `(a : ℝ) * u₁.val = (b : ℝ) * u₂.val`.
- `HasCommonUnitCoordinates` packages two coordinates for one real point.
- `syncCoordinates_have_common_point` constructs the canonical point.
- `syncCoordinates_multiple_has_common_point` constructs every fiber multiple.
- `commonCoordinates_cross_mul` proves `b*m = a*n`.
- `commonCoordinates_divisible_by_syncCoordinates` proves `a ∣ m` and
  `b ∣ n` from coprimality.
- `commonCoordinates_eq_sync_mul` proves the main fiber theorem.
- `commonCoordinates_iff_sync_mul` supplies the converse and preferred iff.
- `sync_mul_parameter_unique` records uniqueness of the parameter.

## Canonical fiber

For a positive coprime synchronization `a*u₁ = b*u₂`, every common coordinate
pair is exactly

```text
(m,n) = (a*t,b*t)
```

for one natural `t`.  The proof sequence is finite and exact:

```text
same real point
  -> b*m = a*n
  -> a ∣ m and b ∣ n
  -> m = a*t and n = b*t
```

The converse constructor proves that every such pair is genuinely common.

## Prime-to-prime consumer

`distinctPrimeSynchronization_unique_primeCoordinatePair` specializes the
fiber to distinct prime synchronization coefficients `p,q`.  If a common
point has prime coordinates `r,s` in the two units, then `t = 1`, so

```text
r = p and s = q.
```

This is a unique prime-to-prime common coordinate pair, not a unique common
lattice point.  The synchronized lattice still contains all pairs
`(p*t,q*t)` for natural `t`; only the pair with both coordinates prime is
unique.

`sameCoordinate_synchronization_unit_eq` handles the edge case where the same
positive coordinate synchronizes both units: the unit values must coincide.

## Regression and semantic boundary

The integer regression uses units `3` and `2` with coefficients `2` and `3`:

```text
2 * 3 = 3 * 2 = 6.
```

No absolute real point is labelled prime or composite.  Prime labels remain
properties of natural coordinates in selected unit universes.

This checkpoint does not classify rational or irrational unit ratios, prove
nonintersection for irrational ratios, introduce generic lattice/module
theory, combine three or more units, define primorial wheels or reduced
residues, or use PowerSwap, GN/CosmicFormula, Legendre, or square anchors.

## Nat.Composite choice

No `Nat.Composite` theorem is needed here.  The checkpoint uses coprime
divisibility and explicit coordinate equalities; later prime-pattern consumers
can reuse the resulting fiber without depending on a particular composite
predicate API.

## Verification

The focused CommonLattice module, the public facade, and the top-level
`DkMath` target were built successfully.  `git diff --check` and prohibited
construct scans were run for the new implementation.  No commit, push, merge,
or CI action was performed.
