# Petal / FloatWindow implementation report: checkpoint 345

## Status

Checkpoint 345 is implemented without adding `sorry` to the modified Lean
files.  The finite signed-mass layer, saturated-successor partition, and
successor-spare injection are now formalized.  The requested stronger
current-window carrier inequality stops at an exact temporal boundary rather
than spending a successor resource before it enters the window.

## Finite numeric-table scope

The finite-transition commentary now distinguishes two architectures:

- a finite projected table with fixed numeric edge weights;
- a finite controller carrying an unbounded symbolic counter or owned
  arithmetic resource.

Lean proves that no single finite projected numeric upper-weight table can
bound the initial canonical drift for every odd root.  The proof uses the
unbounded all-ones family and permits arbitrary finite source and target
signatures.  It does not assert a fixed-root impossibility and does not rule
out finite symbolic control.

## Exact signed masses

The new module `CanonicalExcursionMass.lean` defines:

```text
canonicalPositiveDriftMass
canonicalNegativeDriftMass
canonicalDynamicPressureMass
canonicalSaturatedTokenCount
```

For every finite interval, Lean proves the exact identity

```text
windowDrift = positiveMass - negativeMass.
```

For an open positive queue excursion, reflection is inactive, hence

```text
queue = positiveMass - negativeMass.
```

Combining this identity with the existing pointwise dynamic-pressure theorem
gives the primary resource inequality

```text
queue + negativeMass <= dynamicPressureMass + saturatedTokenCount.
```

No future queue zero is assumed.

## Saturated-successor classification

Saturated tokens are partitioned by priority into four finite sets:

1. negative successor;
2. nonnegative successor with an actual spare selected incidence;
3. zero-rigid successor;
4. tight-positive-rigid successor.

Lean proves membership normal forms, exhaustiveness, pairwise disjointness,
and the exact cardinal identity

```text
saturatedTokenCount
  = negativeCount + spareCount + rigidResidualCount,

rigidResidualCount = zeroRigidCount + tightRigidCount.
```

A negative successor cancels the predecessor unit pointwise:

```text
1 + successorDrift <= 0.
```

The two rigid classes remain explicit.  They are not hidden in a potential.

## Successor-spare injection

For each spare-class saturated token, Lean chooses one actual spare selected
incidence in its successor block.  The target is a dependent-pair carrier that
retains both successor block index and source incidence.  Equality of images
therefore forces equality of successor indices and then predecessor indices.

Consequently:

```text
card saturatedSpareIndices
  <= Nat.card globalSuccessorSpareCarrier.
```

No incidence can be reused by two saturated tokens.

## Exact stopping obstruction

The signed masses for an open excursion through block `m` cover `q..m`, while
the successor classification covers successor blocks `q+1..m+1`.  If block
`m` is saturated, its negative cancellation or spare incidence belongs to
block `m+1`, outside the current mass interval.

Thus the proposed replacement

```text
queue + negativeMass
  <= selectedPressureCarrierCard + rigidResidualCount
```

is not presently contribution-preserving.  It would silently spend a future
resource for a terminal saturated token.  The source code records two honest
continuations:

1. restrict successor charging to `k < m` and retain terminal saturation as a
   boundary residual;
2. extend the accounting horizon through `m+1` and prove queue transport to
   that enlarged window.

This is the first genuine cp-345 stopping obstruction.  The exact partition,
pointwise cancellation, and injection remain valid finite certificates.

## Finite audit

The Python audit was extended and rerun over all 8,192 odd roots in
`1..16383`, with at most 4,096 blocks per root.  Every root reached a
state-one canonical endpoint within this finite run.

At every positive queue state the audit checked:

- the active-window absorption-deficit identity;
- `queue = positiveMass - negativeMass`;
- `positiveMass <= dynamicPressureMass + saturatedCount`.

The CSV stores the richer data for each root's maximum witness.  Across the
6,709 positive maximum witnesses it observed:

```text
largest queue:                     8
largest positive drift mass:      11
largest negative drift mass:       5
total saturated tokens:          781
internal negative successors:      0
internal spare successors:        52
internal zero-rigid successors:   29
internal tight-rigid successors:   0
terminal successor pending:      700
largest spare carrier count:       3
```

The 700 pending cases are not failures of classification.  Their successor is
outside the recorded maximum window and is intentionally not charged.  These
figures are finite observations only; they imply no all-time frequency or
uniform bound.

## Branch decision

The immediate continuation should make the temporal contract explicit before
attacking rigid grammar.  The most local route is an internal-token theorem
for saturated `k < m` plus a one-bit terminal saturation residual.  Only after
that theorem should the selected carrier and rigid count replace the raw
saturated count in the open-window inequality.

The audit suggests zero-rigid successors are the observed internal rigid
branch and tight-rigid successors did not occur among maximum witnesses, but
this finite pattern must not be promoted to a theorem.

## Verification

The following gates pass:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
python3 python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
python3 -m py_compile python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
git diff --check
```

Generated audit files:

```text
python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.csv
python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.md
```
