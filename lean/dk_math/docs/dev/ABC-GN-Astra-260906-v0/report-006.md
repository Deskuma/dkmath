# LUNA-006 — realized cubic modulus-space extraction

## Result

LUNA-006 is implemented.  The canonical realized cubic large profiles now
map injectively to a finite set of distinct natural-number joint moduli.  The
cubic modulus moment is rewritten exactly as a sum over that set, and every
member carries a positive interval witness, a repeated-part identity, and the
resulting quadratic divisor certificate.

No estimate for the resulting modulus sum was attempted.

## Files changed

- `DkMath/ABC/GNExcessCubicRealizedModuli.lean` — new production module.
- `DkMath/ABC/GNExcessCubicRealizedBoundary.lean` — corrected the LUNA section
  title from `Final LUNA-004 composition` to `Final LUNA-005 composition`.
- `DkMath/ABC.lean` — imports the new module immediately after
  `GNExcessCubicRealizedBoundary`.
- `README.md` and `ROADMAP.md` — record the completed checkpoint.
- This report.

## Factorization coordinates and injectivity

`GNExcessJointDepthModulus_factorization_at` proves that, for every prime
family coordinate `q`, the factorization exponent of the joint modulus is
`excess(q) + 1` when the coordinate is active and zero otherwise.  The proof
uses the existing expanded product formula and `Nat.factorization_prod`.

`GNExcessJointDepthModulus_injective` is generic for any finite prime family.
It handles inactive coordinates explicitly, then recovers each positive
coordinate from the factorization exponent and concludes by function
extensionality.

## Distinct modulus space and exact moment rewrite

`GNExcessCubicRealizedLargeModulusSpace X` is the image of the realized
canonical cubic large-profile space under `GNExcessJointDepthModulus`.
`mem_GNExcessCubicRealizedLargeModulusSpace_iff` exposes its witness profile
and modulus equality.

`card_GNExcessCubicRealizedLargeModulusSpace` proves cardinal preservation by
profile-to-modulus injectivity.  The exact identity
`GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace` uses
`Finset.sum_image`, so the LUNA-005 moment is now a sum over distinct natural
numbers.

No optional packet structure was added; the existing
`GNExcessLargeBoundaryPacket` API supplies the needed arithmetic facts.

## Witness and arithmetic certificate

`GNExcessCubicRealizedLargeModulusSpace_exists_witness` extracts a positive
`a ∈ Finset.Icc 0 X` and proves

```text
M = GNNonExceptionalRepeatedPart 3 a 1.
```

The divisibility consumers prove both

```text
M ∣ GN 3 a 1
M ∣ a^2 + 3*a + 3.
```

The extracted modulus API also proves, for every member `M`:

```text
X + 1 < M
M ≤ 3 * (X + 1)^2
0 < M
```

and, for every prime `q ∣ M`:

```text
q^2 ∣ M
q % 3 = 1.
```

The squareful and mod-three statements reuse the repeated-part support and
existing cubic support-order theorems.

## Final human-readable bridge

`exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_realizedModuli`
rewrites the LUNA-005 endpoint as

```text
actual cubic moment
≤ 2 * (X + 1) * finiteEuler
  + ∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X, M^(3/8).
```

This is an exact extraction and reindexing result, not a bound for the final
sum.

## Verification

From `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessCubicRealizedModuli
lake build DkMath.ABC
```

Both builds completed successfully.  The focused module build completed 8787
jobs and the ABC aggregator build completed 8844 jobs.  The existing warning
at `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6` is unrelated
and outside the changed modules.

The changed Lean files contain no `sorry`, `admit`, or new `axiom`, and no
reference to `abc_main_axiom`.  The principal factorization, injectivity,
modulus-moment rewrite, quadratic-divisor, and final bridge theorems were
checked with `#print axioms`; their dependencies are only

```text
propext, Classical.choice, Quot.sound
```

## Remaining mathematical blocker

The frontier is now the arithmetic estimate for

```text
∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X, M^(3/8).
```

The formalization does not claim that distinct interval points give distinct
moduli, nor that every squareful divisor of `a^2 + 3*a + 3` is realized.  The
next research question is how to control this distinct realized-modulus sum
using its interval, quadratic-divisor, squareful, and mod-three constraints.
