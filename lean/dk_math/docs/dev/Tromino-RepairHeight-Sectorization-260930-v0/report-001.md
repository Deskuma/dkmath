# report-001 — RepairDistance + StateSector generic kernels

## Outcome

Outcome A. `RepairDistance` and `StateSector` are production-proved, the
finite regressions build, and the generic unit-slope and sectorization
theorems are complete. Instruction-002 may begin the concrete Kempe
integration.

## Files changed

Production:

- `DkMath/Tromino/RepairDistance.lean`
- `DkMath/Tromino/StateSector.lean`

Tests and audits:

- `DkMathTest/Tromino/RepairDistanceRegression.lean`
- `DkMathTest/Tromino/StateSectorRegression.lean`
- `DkMathTest/Tromino/RepairDistanceAxiomAudit.lean`
- `DkMathTest/Tromino/StateSectorAxiomAudit.lean`

## RepairDistance API

`Steps step n x y` is an inductive exact-length path relation with
`Steps.zero` and `Steps.prepend`; the successor length is represented as
`n + 1`. The algebra provided is `Steps.refl`, `Steps.prepend`,
`Steps.concat`, `Steps.add`, and `Steps.reverse_of_symmetric`.

`CanExitAt step exit n x` means that there is an exit state reachable from
`x` in exactly `n` steps. `repairHeight step exit x hreachable` is
`Nat.find hreachable`, where `hreachable : ∃ n, CanExitAt step exit n x`.
Unreachable states therefore have no `repairHeight` value in this kernel.

The zero-height exit convention is proved by
`repairHeight_eq_zero_of_exit`. The minimum facts are:

- `repairHeight_spec`
- `repairHeight_minimal`

The directed unit-slope theorem is `repairHeight_le_succ_of_step`; the public
paired theorem is `repairHeight_unit_slope`. Symmetry is required only for the
reverse inequality.

## StateSector API

`Restricted R A x y` is exactly `A x ∧ A y ∧ R x y`. Symmetry preservation
is `restricted_symmetric`.

Rooted reachability is
`Reachable R root x := ∃ n, Steps R n root x`. The exact path transport lemma
is `steps_iff_of_iff`, and the sectorization theorem is
`reachable_iff_restricted`; the packaged public form is
`chamber_sectorization`.

Because `Restricted` requires both endpoints to be admissible, zero-step
reachability still requires an admissible root when reasoning about a
restricted chamber. This boundary is explicit in the definition and is
exercised by the sector regression.

## Finite regressions

`RepairDistanceRegression` uses a three-state path with the left endpoint as
the exit. It proves the kernel-checked heights `0`, `1`, and `2`, and checks
both unit-slope inequalities on the middle/right edge.

`StateSectorRegression` uses a four-state parent relation. Admissibility keeps
the root and one allowed state, while the blocked branch is removed. It proves
the allowed state is in the rooted child chamber, the blocked state is not,
and checks the generic sectorization theorem.

## Axiom audits

The focused audit output was:

- `Steps.concat`, `Steps.reverse_of_symmetric`: `propext`.
- `repairHeight_spec`, `repairHeight_minimal`,
  `repairHeight_unit_slope`: `propext`, `Classical.choice`, `Quot.sound`.
- `restricted_symmetric`: no axioms.
- `steps_iff_of_iff`, `reachable_iff_restricted`,
  `chamber_sectorization`: `propext`.

No new axiom declaration was added.

## Validation

All required focused builds passed:

```text
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
lake build DkMathTest.Tromino.RepairDistanceRegression
lake build DkMathTest.Tromino.StateSectorRegression
lake build DkMathTest.Tromino.RepairDistanceAxiomAudit
lake build DkMathTest.Tromino.StateSectorAxiomAudit
```

`git diff --check` passed. The supplemental no-index check for the new
untracked report also produced no whitespace diagnostics. The changed Lean
files had no matches for `sorry`, `admit`, a new `axiom` declaration, or
`unsafe`.

The only implementation deviation is using the repository's available
`Symmetric` predicate, which Lean 4.34 reports as deprecated in favor of
`Std.Symm`; its explicit symmetry hypothesis and semantics are unchanged.
No concrete coloring bridge, `KempeRepair.lean`, broad Tromino module, or
Four Color endpoint was added.

## Recommendation for instruction-002

Proceed with `KempeRepair.lean`: prove the proper one-point recolor to
singleton two-color Kempe component bridge using the existing concrete
Tromino state, exchange, and graph-coloring modules, then instantiate
`repairHeight_unit_slope`. Keep cross-topology height preservation and any
universal coloring claim outside the next checkpoint.
