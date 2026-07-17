# Petal / FloatWindow Report cp-326

## Status

`cp-326` closes the local claim-hole, successor-source, and abstract dyadic
budget program without `sorry`.  The branch stops at the first genuine global
resource obstruction: the current upper-window API has no finite,
nonreusable carrier of upper-boundary bit positions.

## Implemented results

### Claim-hole accounting

`canonicalBlockClaimHoles` is the complement of the payment claim depths in
the complete depth interval.  Lean now proves disjointness, exact union, and

```text
claimCount + claimHoles.card = blockLength.
```

The primary signed normal form is therefore

```text
endpointAccountingTerm
  = blockLength - terminalValuation - claimHoles.card.
```

This one formula controls saturation, balanced blocks, positive spare
cardinality, and tight valuation-one blocks.

### Exact rigid and spare classes

The selected spare carrier has exact cardinality:

```text
terminal valuation = 1  -> holes.card - 1
terminal valuation >= 2 -> holes.card.
```

The zero-carrier balanced class has exactly two normal forms:

1. `length = terminal valuation` and every depth is claimed;
2. `terminal valuation = 1`, `length = 2`, and exactly one depth is claimed.

A singleton claim hole has a chosen unique missing depth, and the claim set is
the complete interval with precisely that depth erased.

### Saturated successor compression

The detailed six-way successor theorem compresses to four source-level cases:

```text
negative drift
or actual spare source
or zero-carrier balanced block
or tight valuation-one positive block.
```

The negative successor numerically cancels the saturated unit.  The spare
branch supplies an actual `Fin 1` embedding into the selected spare incidence
carrier.  Thus the valuation-one nonempty-spare branch is discharged and is
not an obstruction.

### Dyadic half-budget

Every positive nonsaturated block has length at least three.  Its selected
dyadic demand satisfies the stronger bound

```text
toNat drift * 2^selectedDepth <= 2^(blockLength - 2).
```

Consequently a saturated mass-two unit and a positive nonsaturated successor
demand fit into the successor budget `2^(blockLength - 1)`.

The numerical statement was strengthened to an explicit abstract carrier:

- `Fin 2` embeds into the low slots;
- the successor demand embeds into the upper half;
- Lean proves every point in the two images is distinct.

This is an abstract potential carrier only.  It is not a carrier of orbit
indices or physical bit positions.

### Length-one residue grammar

For a saturated predecessor, a successor of length one forces

```text
canonicalBlockOddCore n k % 8 = 3.
```

The `% 16 = 11` candidate needs one additional algebraic bridge: an explicit
formula transporting the predecessor odd core through the successor odd core
into the successor terminal carrier.  Existing APIs expose the successor
start and length separately but not this substituted terminal-carrier normal
form.  No empirical residue claim was substituted for that missing theorem.

## Genuine obstruction

The upper-window modules currently expose scalar width/carry and eventual-zero
facts.  They do not expose any of the following:

- a finite carrier of distinct upper-zero bit positions;
- a finite binary refinement tree rooted at a boundary position;
- a uniform multiplicity theorem preventing reuse of one boundary resource by
  several block budgets.

Therefore the abstract dyadic leaves cannot yet be transported to a finite
nonreusable initial-state resource.  A global repayment or convergence claim
does not follow from the present local bounds.

## Next implementation

The next sound layer should first define a concrete upper-boundary resource
carrier and prove its nonreuse invariant.  Separately, the local arithmetic
branch can add the successor odd-core/terminal-carrier substitution theorem
needed to decide the candidate `% 16 = 11` residue implication.

Do not begin a global matcher until at least one of those two interfaces is
available.

## Verification

The targeted module build passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
```

The complete gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The top-level build replays known `sorry` warnings in unrelated research
modules.  This checkpoint adds no `sorry` and no `maxHeartbeats` override.
