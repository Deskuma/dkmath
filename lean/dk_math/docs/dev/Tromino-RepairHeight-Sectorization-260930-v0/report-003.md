# report-003 — admissible repair chamber integration

## Outcome

Outcome A. Explicit admissible-root chamber semantics, admissible concrete
singleton-Kempe steps, same-carrier child-step sectorization, and full-graph
repair-height unit slope across chamber edges are all production-proved.

The remaining frontier is concrete child-topology/state transport and/or a
later application-supplied Missing-valid predicate.

## Files changed

- `DkMath/Tromino/RepairChamber.lean`
- `DkMathTest/Tromino/RepairChamberRegression.lean`
- `DkMathTest/Tromino/RepairChamberAxiomAudit.lean`
- `docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-003.md`

The frozen RepairDistance, StateSector, and KempeRepair production modules
were reused without modification.

## Admissible chamber semantics

`AdmissibleChamber R A root x` is defined as

```text
A root ∧ Reachable (Restricted R A) root x
```

This explicitly corrects the zero-step boundary: raw
`Reachable (Restricted R A) root root` always holds by `Steps.zero`, including
when `A root` is false. The root admissibility condition is carried separately
by `AdmissibleChamber`.

The exported theorems are:

- `admissibleChamber_root_iff`;
- `restricted_reachable_target_admissible`;
- `admissibleChamber_target`;
- `admissibleChamber_reachable`.

Thus chamber membership implies target admissibility and restricted-step
reachability, while root membership is equivalent to root admissibility.

## Concrete admissible singleton-Kempe step

`AdmissibleSingletonKempeStep G mutable admissible` is exactly

```text
Restricted (SingletonKempeStep G mutable) admissible
```

Its symmetry theorem is
`admissibleSingletonKempeStep_symmetric`, obtained from the frozen
`singletonKempeStep_symmetric` and `restricted_symmetric` facts.

`onePointRecolor_admissibleSingletonKempeStep` proves that a proper one-point
recolor with admissible source and target endpoints gives an admissible
singleton-Kempe step. The `admissible` predicate remains the generic
application boundary; no Python `MissingColor` solver structure was invented.

## Concrete chamber and sectorization

`SingletonKempeRepairChamber G mutable admissible root x` is the explicit
`AdmissibleChamber` for the full `SingletonKempeStep G mutable` relation.

Its interface theorems are:

- `singletonKempeRepairChamber_root_iff`;
- `singletonKempeRepairChamber_target`;
- `singletonKempeRepairChamber_reachable`.

`childStep_reachable_iff_singletonKempeRepairChamber` packages the
same-carrier sectorization interface. Given admissible `root` and a pointwise
equivalence between `childStep` and `AdmissibleSingletonKempeStep`, it proves

```text
Reachable childStep root x
  ↔ SingletonKempeRepairChamber G mutable admissible root x.
```

This theorem starts after child state/topology transport has already been
supplied. It does not claim that arbitrary child topologies admit such a
transport.

## Two-graph unit-slope theorem

`admissibleSingletonKempeStep_repairHeight_unit_slope` projects the restricted
chamber edge to its underlying full `SingletonKempeStep` edge and reuses
`singletonKempe_repairHeight_unit_slope`.

The height in this theorem is explicitly the height in the full repair graph:

```text
repairHeight (SingletonKempeStep G mutable) exit ...
```

It is not a height on the restricted chamber graph. No shortest repair path is
claimed to remain admissible.

## Finite regression

`RepairChamberRegression` reuses the small `Fin 2` proper-coloring fixture
from checkpoint 002 and adds a third proper coloring plus an admissibility
predicate requiring the second vertex to have the shared endpoint color. It
proves:

1. an admissible root belongs to its explicit chamber;
2. an inadmissible root is outside the explicit chamber even though raw
   restricted zero-step `Reachable` holds;
3. a one-point recolor with two admissible endpoints gives an admissible
   restricted step;
4. an inadmissible endpoint blocks the restricted edge;
5. the concrete child-step/restricted-parent sectorization interface;
6. full repair-height unit slope across the admissible chamber edge.

No W9 state, sector census, or BFS implementation was added.

## Axiom audit

The focused audit reports:

- `admissibleChamber_root_iff`: no axioms;
- `admissibleChamber_target`: no axioms;
- `admissibleSingletonKempeStep_symmetric`,
  `onePointRecolor_admissibleSingletonKempeStep`,
  `childStep_reachable_iff_singletonKempeRepairChamber`, and
  `admissibleSingletonKempeStep_repairHeight_unit_slope`:
  `propext`, `Classical.choice`, `Quot.sound`.

No new axiom declaration was added.

## Validation

Focused builds passed:

```text
lake build DkMath.Tromino.RepairChamber
lake build DkMathTest.Tromino.RepairChamberRegression
lake build DkMathTest.Tromino.RepairChamberAxiomAudit
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
lake build DkMath.Tromino.KempeRepair
```

`git diff --check` passed. The supplemental no-index check for the new
untracked report produced no whitespace diagnostics. The changed Lean files
had no matches for `sorry`, `admit`, a new `axiom` declaration, or `unsafe`.

Warnings were separated from failures: Lean 4.34 reports the existing
`Symmetric` deprecation in the frozen and new symmetry interfaces, and the
small finite coloring fixtures emit non-failing flexible-`simp_all` linter
warnings. All focused builds completed successfully.

## Deviations and non-goals

No deviation from the requested semantic boundary was needed. `Reachable` and
`Steps.zero` were not changed. No concrete Python-compatible MissingColor
state, child-to-parent topology equivalence, cross-topology height claim,
child-height comparison, height-label preservation, general non-singleton
Kempe chain, W9 enumeration, six-sector theorem, universal colorability, Four
Color theorem, or Port-chain modification was added.

## Remaining frontier after checkpoint 003

The remaining work is application-specific: provide a concrete
Missing-valid/admissibility predicate when its state-space policy is fixed,
and prove any child-topology/state projection or equivalence needed to use
the same-carrier sectorization interface. Cross-topology repair-height
monotonicity and universal coloring claims remain outside this checkpoint.
