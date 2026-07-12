# Petal implementation report cp-292

## Implemented

The finite-window layer now distinguishes internal pairs from boundary pairs.

- `SourcePressureCanonicalInternalPairCoverageInWindow` requires both the
  left and right centers of an adjacent pair to lie in the window.
- `sourcePressureUnresolvedInternalPairFamily` contains exactly the in-window
  adjacent pairs that are not canonical packing states.
- Its membership theorem and left-endpoint image are available.
- Internal coverage implies that the unresolved internal pair family is empty.
- `sourcePressureCanonicalPackingUnitFamily` names the previously repeated
  `attach.image` construction, and its cardinality is equal to the canonical
  pair family cardinality.

The `zip`/adjacency conversion is now proved in both directions, so the
unresolved-family emptiness theorem is a genuine list-recursive result rather
than a definitional shortcut.

## Mathematical status

The positive residue is now conceptually split as:

```text
positive residue
  = unresolved internal left endpoints
  + right-boundary / terminal residue
```

The first component has a precise Finset carrier and vanishes under the new
internal coverage contract.  The second component is not yet encoded: proving
its cardinality bound requires a separate theorem that at most one adjacent
pair crosses `hi`, at most one terminal witness exists, and those two cases do
not coexist as distinct in-window witnesses.

## Producer inspection

The current BeamSeed, SortedFailure, and FailureResolution states remain
existential pair producers.  They do not establish internal coverage for every
member of `L.zip L.tail`.  Therefore no unconditional `residue.card ≤ 1` or
endpoint-corrected `+ 1` theorem is asserted here.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

The new code introduces no `sorry` or `axiom`. Existing unrelated project
warnings remain unchanged.

## Next target

Add explicit right-boundary and terminal Finsets, then prove their cardinality
bound under sorted-before. After that, combine it with the unresolved internal
family to obtain the endpoint-corrected local-Big theorem.
