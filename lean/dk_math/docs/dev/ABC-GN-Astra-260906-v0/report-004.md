# LUNA-004 — ghost-free realized moment bridge

## Result

LUNA-004 is implemented. The pointwise exponential moment is now reindexed
over the exact realized profile image. Its small contribution is enlarged to
the historical small-density majorant, while its large contribution is summed
only over `GNExcessRealizedLargeBoundaryProfileSum`. The historical raw-large
moment theorems remain unchanged.

No bound for the realized large-boundary sum was attempted.

## Files changed

- `DkMath/ABC/GNExcessRealizedMoment.lean` — new production module.
- `DkMath/ABC.lean` — imports the new module after
  `GNExcessRealizedFibers`.
- `README.md` and `ROADMAP.md` — record the completed LUNA-004 checkpoint.
- This report.

## Declarations added

The new module provides:

- `exp_GNExcessMassAt_sum_eq_realizedFiberSum`.
- `GNExcessRealizedSmallProfileSpace` and
  `GNExcessRealizedSmallDensityProfileSum`.
- `mem_realizedSmallProfileSpace_iff` and
  `realizedSmallProfileSpace_subset_smallProfileSpace`.
- `GNExcessRealizedSmallDensityProfileSum_le`.
- `mem_realizedLargeProfileSpace_iff_realized_and_large` and
  `realizedLargeProfileSpace_eq_realizedProfileSpace_filter_large`.
- `realizedProfileSpace_eq_small_union_large` and
  `disjoint_realizedSmallProfileSpace_realizedLargeProfileSpace`.
- `exp_GNExcessMassAt_sum_le_small_add_realizedLarge`.
- `exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge`.
- `exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic`.

## Exact weighted identity

The new reindex theorem proves

```text
∑ a ∈ Finset.Icc 0 X,
  exp (t * GNExcessMassAt Q p b a)
=
∑ excess ∈ GNExcessRealizedProfileSpace Q p b X,
  (GNExactExcessProfileEvent Q excess p b X).card
    * exp (t * GNExcessActiveProfileMass Q excess).
```

It uses the exact realized image and
`GNExcessMassAt_eq_activeProfileMass` on each fiber; the rectangular formal
profile space is not used for reindexing.

## Realized split and moment bridge

Under `0 < b`, every realized profile belongs to exactly one of the realized
small and realized large spaces. The large membership theorem identifies the
large space with the realized image filtered by
`X + 1 < GNExcessJointDepthModulus`.

The main ghost-free bound is

```text
pointwise moment
≤ 2 * (X + 1) * GNExcessSmallDensityProfileSum
  + GNExcessRealizedLargeBoundaryProfileSum.
```

The finite-Euler variant follows directly from
`GNExcessSmallDensityProfileSum_le_finiteEulerDensity`. A canonical cubic
specialization for
`GNNonExceptionalIntervalPrimeFamily 3 1 X` was added using the existing
prime-family hypotheses.

The old theorems
`exp_GNExcessMassAt_sum_le_small_add_large` and
`exp_GNExcessMassAt_sum_le_finiteEuler_add_large` were not modified.

## Verification

From `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessRealizedMoment
lake build DkMath.ABC
```

Both builds completed successfully. The focused module build completed 8784
jobs, and the ABC aggregator build completed 8842 jobs.

The changed Lean module contains no `sorry`, `admit`, or `axiom`, and no
reference to `abc_main_axiom`. The existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6` is unrelated and
outside the changed module.

The exact weighted identity, the small-plus-realized-large theorem, and the
finite-Euler variant were audited with `#print axioms`; their dependencies are
only the standard boundary

```text
propext, Classical.choice, Quot.sound
```

## API friction and remaining boundary

The finite-sum proof reused `Finset.sum_fiberwise_of_maps_to` and the existing
small/large fiber cardinal estimates. The only bookkeeping adjustment was to
unfold the realized boundary shell before rewriting its profile filter.

The remaining mathematical blocker is unchanged: control the product of a
realized large fiber cardinality and its realized large-profile weight. This
checkpoint stops before any bound for that term, density theorem, or ABC
quality coupling.
