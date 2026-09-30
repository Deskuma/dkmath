# Tromino Repair Height Sectorization — instruction-007 closeout

Date: 2026-10-01

## Overall outcome

Outcome A. The frozen OBS-019 neighbor-01 case is kernel-calibrated against
the generic rooted chamber transport. The campaign is complete and ready for
PR review.

This closeout adds only test and documentation artifacts. No production
theorem or module was added.

## Frozen source data

The calibration was checked against the committed artifacts:

- `python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md`;
- `python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/summary.json`;
- `python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/summary.json`;
- `python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/neighbor-01.json`;
- `python/Tromino/results/repair-depth/w9-state-component-v24/summary.json`;
- `python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json`;
- parent state files `state-008.json`, `state-010.json`, `state-012.json`, and
  `state-014.json`.

The frozen provenance is:

```text
seed:              11000009
step:              16
neighbor:          1
move:              [4, 21, 5, 17]
mutable order:     [4,5,8,9,10,12,13,14,15,17,18]
child states:      4
parent state ids:  [8,10,12,14]
child baseline:    index 2 -> parent state 12
child edges:       (0,3), (1,2), (2,3)
parent edges:      (8,14), (10,12), (12,14)
parent heights:    8->9, 10->9, 12->10, 14->9
```

The Python color decoder used in the test is the explicit finite map
`0 -> (0,0)`, `1 -> (0,1)`, `2 -> (1,0)`, `3 -> (1,1)`.

## Test artifacts

Added:

- `DkMathTest/Tromino/OBS019Neighbor01Calibration.lean`;
- `DkMathTest/Tromino/OBS019Neighbor01AxiomAudit.lean`;
- this report.

The calibration module defines the four child rows and their four matched
parent rows over `Fin 11`, proves the exact projected edge relation, and
builds a local `RootedChamberTransport` packet. It proves:

- all four child states are reachable from child root `2`;
- all four mapped parent states are in the rooted admissible chamber at
  parent state `12`;
- child reachability is equivalent to membership in that parent chamber;
- the child edge set maps exactly to the parent induced edge set;
- the baseline projection is parent state `12`.

The finite rows reproduce the four frozen child projections:

```text
[0,3,1,1,1,0,0,1,0,1,3]
[0,3,1,1,1,0,1,0,0,1,3]
[0,3,1,1,1,0,3,0,0,1,3]
[0,3,1,1,1,0,3,1,0,1,3]
```

The child-to-parent row matching is respectively `0 -> 8`, `1 -> 10`,
`2 -> 12`, and `3 -> 14`.

The frozen parent height labels are also recorded as data-only constants in
the test (`8 -> 9`, `10 -> 9`, `12 -> 10`, `14 -> 9`). No height theorem is
claimed or derived from these labels.

## Axiom audit

The audit shows that the generic transport theorems do not depend on axioms.
The finite test proofs use only the standard `propext` dependency introduced
by proposition extensionality; no new axiom declaration was added.

## Validation

Successful focused builds:

```text
lake build DkMathTest.Tromino.OBS019Neighbor01Calibration
lake build DkMathTest.Tromino.OBS019Neighbor01AxiomAudit
lake build DkMath.Tromino.RestorationFlipTransport
lake build DkMath.Tromino.RestorationRepairState
lake build DkMath.Tromino.StateProjectionTransport
```

Additional checks:

- `git diff --check` passed;
- the changed Lean files contain no `sorry`, `admit`, `axiom`, or `unsafe`;
- the report and documentation changes have no whitespace diagnostics;
- the authoritative JSON files were not regenerated or modified.

## Explicit non-goals

This closeout does not claim a full W9 proof, all six OBS-019 cases, a
universal preserving-flip transport theorem, repair BFS, height preservation
or a height theorem, the Four Color Theorem, or Port triangulation closure.
The frozen case is a finite calibration witness for the already-formalized
transport abstraction.

## Status

```text
TRH-009: COMPLETE / APPROVED — Outcome A
campaign: COMPLETE / READY FOR PR
```
