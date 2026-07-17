# Petal / FloatWindow Report cp-347

## Scope

This checkpoint split internal spare successors by drift sign and absorbed
only the strictly positive branch into the existing positive-only global
selected carrier.  It did not introduce a general carrier framework or alter
the rigid successor grammar.

## Finite diagnostic

The existing canonical excursion audit was extended without changing its CSV
schema.  Over odd roots `1..16383`, its record-window observations counted:

- zero-drift internal spare successors: `11`;
- positive-drift internal spare successors: `85`.

The first observed zero-drift spare witness was:

```text
root = 3931
record window = 0..3
predecessor block = 0
successor block = 1
successor drift = 0
spare cardinality = 1
```

This is finite evidence only.  It does establish the branch decision for the
implementation: a zero-drift-spare impossibility route is not supported by the
audit.  Removing that residual later requires an augmented selected-arrival
carrier that explicitly admits zero-drift blocks.

## Lean results

`CanonicalExcursionOwnership.lean` now provides:

- exact zero/positive internal spare sets, union, disjointness, and card split;
- a block-preserving charge from each positive-spare predecessor into the
  actual spare complement of its successor selected carrier;
- one injection combining all same-block drift-image incidences with those
  predecessor charges;
- exact positive-mass decomposition into drift images and saturated units;
- the improved current-window ownership theorem
  `queue_le_globalSelected_add_zeroSpare_rigid_terminal`.

The resulting proved inequality is:

```text
queue(m)
  <= Nat.card CanonicalGlobalSelectedPressureCarrier
     + internalZeroSpareCount
     + internalRigidResidualCount
     + terminalSaturatedIndicator
```

The positive-spare count has disappeared.  It is not merely bounded
numerically: its incidences are disjoint from the selected drift image inside
each successor block, and retaining the sigma block coordinate prevents reuse
across blocks.

## Facts established

1. Every internal spare successor has drift exactly zero or strictly positive.
2. Positive-spare predecessor tokens consume unused incidences already present
   in the positive successor block's selected carrier.
3. These charges do not collide with positive drift-image incidences.
4. The remaining zero-spare term is a genuine type boundary of the current
   positive-only carrier, not an algebraic proof artifact.

No rootwise queue bound, eventual discharge theorem, or orbit-wide conclusion
is claimed.

## Verification

Completed during the checkpoint:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
python3 python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
git diff --check
```

All build and whitespace gates passed.  The modified Wall/Ownership file adds
no `sorry`.

## Next implementation inference

The next honest branch is not another positive-drift absorption theorem.  It
is a narrowly scoped zero-drift selected-arrival carrier whose index contract
includes exactly the observed zero-spare source class.  Before implementing
it, the local source theorem should identify which zero-drift selected
incidences are available without allowing arbitrary zero-drift blocks into the
global carrier.  Rigid residual persistence remains a separate later branch.
