# Petal / FloatWindow implementation report: checkpoint 346

## Status

The temporal split and internal negative-payment stages are proved without
`sorry`.  The requested final ownership theorem exposed a type-level mismatch
in Stage C, so the strongest contribution-preserving theorem justified by the
current carrier API was proved instead.

## Exact temporal split

The new module `CanonicalExcursionOwnership.lean` defines internal saturated
indices by erasing the right endpoint `m`.  Since every remaining index is
strictly below `m`, its successor lies inside the current window.

Lean proves exactly:

```text
saturatedTokenCount
  = internalNegativeCount
  + internalSpareCount
  + internalRigidCount
  + terminalSaturatedIndicator.
```

Here `internalRigidCount` remains the explicit sum of zero-rigid and
tight-positive-rigid classes.  The terminal indicator is either zero or one,
and Lean proves it is at most one.

## Internal negative payment

Each internal negative token at `k` is mapped to one negative-mass unit at
`k+1`.  The proof establishes:

- `k < m`, hence `k+1 <= m`;
- `q <= k`, hence `q <= k+1`;
- a negative integer drift contributes at least one unit of negative mass;
- `k -> k+1` is injective.

Therefore:

```text
internalNegativeCount <= canonicalNegativeDriftMass n q m.
```

No resource from block `m+1` is used.

## Ownership theorem obtained

Combining signed-mass equality, the existing selected-carrier bound, internal
negative payment, and the exact temporal split gives:

```text
queue at m
  <= Nat.card (CanonicalGlobalSelectedPressureCarrier n q m)
     + internalSpareCount
     + internalRigidResidualCount
     + terminalSaturatedIndicator.
```

This is a strictly current-window theorem.  It removes the internal negative
class completely and reduces the temporal boundary to one bit.

## Stage C correction

The instructed embedding of every internal spare token into
`CanonicalGlobalSelectedPressureCarrier n q m` is not well typed from the
current hypotheses.

The existing global carrier is indexed only by positive-drift blocks.  The
existing saturated-successor classification explicitly permits:

```text
successor drift = 0
and
selected pressure carrier is nonempty.
```

That branch is classified as `CanonicalSuccessorSpareAvailable`, but its block
is absent from `canonicalPositiveDriftBlockIndices`, so its incidence cannot
retain its block coordinate in the requested positive-only sigma carrier.

Removing `internalSpareCount` now requires one additional contract:

1. enlarge the global selected carrier to include zero-drift selected blocks;
   or
2. prove zero-drift spare successors impossible in open positive excursions.

Neither statement currently exists.  The source comment records this exact
boundary.  No arbitrary cross-block cardinal allocation was substituted for
the requested contribution-preserving map.

## Facts now fixed

1. All nonterminal saturated tokens have successors inside the observed
   window.
2. Internal negative successors pay distinct predecessor units from current
   negative mass.
3. The only temporal residual is the possible saturated token at `m`, bounded
   by one.
4. The remaining ownership gap is not negative payment or temporal reuse.  It
   is specifically ownership of zero-drift spare selected incidences.

## Verification

The following gates pass:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The checkpoint does not modify the Python audit.
