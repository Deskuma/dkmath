# Petal / FloatWindow implementation report - checkpoint 322

## Result

The fixed-depth accounting layer now distinguishes three finite objects:

1. selected bucket mass;
2. minimal selected residual after exact-length charge;
3. full pressure amplitude, which may include unselected continuation mass.

All added Lean declarations are no-sorry.

## Structural cleanup

`CanonicalActiveSelectedPressureBucketCarrier` indexes only positive,
nonsaturated blocks.  It is explicitly equivalent to the old selected bucket:
a saturated block cannot carry a selected incidence because its selected
carrier is empty.

An explicit global equivalence decomposes the global selected carrier into the
dependent sum of active depth buckets.  It preserves block and source-incidence
coordinates rather than merely proving equal cardinalities.

## Exact-length charge

`CanonicalExactLengthTokenCarrier` packages exact-length block tokens over all
active depths.  Forgetting depth is injective because each block has one unique
canonical length.  Consequently its cardinality is at most `m - q + 1` when
`q <= m`.

## Minimal residual

At depth `d`, the new residual count is

```text
active selected bucket count - exact-length block count.
```

The active bucket embeds into exact-length tokens plus these residual units.
The residual units in turn embed into full pressure-amplitude units.  This
second target is intentionally described as upper capacity: it can contain
continuation incidences that were never selected.

## Global finite reduction

The primary theorem is now

```text
global selected carrier
  <= block interval cardinality + selected residual carrier.
```

The full-amplitude version is only a coarser corollary.  Combined with the
existing saturated-token packing theorem, positive-drift units are bounded by

```text
block count + minimal selected residual + saturated half-packing term.
```

Thus the smallest genuinely uncontrolled mass is the selected residual, not
the full pressure amplitude.

## First stopping obstruction

The next requested sliding identity is mathematically consistent with the
block decomposition, but two caller-facing bridges are absent:

- a finite-sum split of block prefixes into `0..q-1` and `q..m`;
- an identification of pressure at `canonicalBlockStartTime n q` with the
  preceding endpoint prefix, including the separate `q = 0` case.

Until these are proved, sliding-window positivity cannot be identified with
the existing absolute-prefix `IsSourcePressureDepth` API.  Likewise, current
local-island packing counts supplied level-zero witnesses and does not control
all superlevel amplitudes.

## Next implementation

Add the prefix-difference bridge in a small separate section or module.  Once
it is established, define distinct prefix and relative amplitude carriers,
then prove the generic finite layer-cake identity without invoking pulse
packing.  Threshold-island generalization should follow only after that API
separation is fixed.
