# report-002 — concrete singleton Kempe bridge

## Outcome

Outcome A. Proper one-point recolor is production-proved to be a singleton
Kempe move, the packaged concrete step relation is symmetric, and its
repair-height unit-slope corollary is proved. Checkpoint 003 may begin
Tromino-facing Missing-valid / chamber integration.

## Files changed

- `DkMath/Tromino/KempeRepair.lean`
- `DkMathTest/Tromino/KempeRepairRegression.lean`
- `DkMathTest/Tromino/KempeRepairAxiomAudit.lean`
- `docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-002.md`

The frozen checkpoint-001 modules were reused without modification.

## Coloring representation

The implementation uses Mathlib's `G.Coloring TrominoState`, where a coloring
is a graph homomorphism into the complete graph on `TrominoState`. Properness
is accessed through `Coloring.valid`. This keeps the graph and coloring
representation native to the available SimpleGraph API and avoids a parallel
explicit properness layer.

## One-point recolor

`OnePointRecolor G mutable source target` is the predicate

```text
∃ v,
  mutable v ∧
  source v ≠ target v ∧
  ∀ u, u ≠ v → target u = source u
```

The witness extraction theorem is `onePointRecolor_witness`; symmetry is
`onePointRecolor_symm`.

## Two-color support and reachability

- `TwoColorSupport c a b x` means `c x = a ∨ c x = b`.
- `TwoColorStep G c a b x y` means graph adjacency plus support at both
  endpoints.
- `KempeReachable G c a b root x` is `Reachable` for `TwoColorStep`, reusing
  the checkpoint-001 `Steps` kernel.

The local exclusion lemma is `not_twoColorStep_at_onePoint`.

## Singleton component theorem

`kempeReachable_singleton_of_onePointRecolor` proves that for the recolor
witness `v`,

```text
KempeReachable G source (source v) (target v) v u ↔ u = v.
```

The proof uses properness of the source to exclude source color `a` at a
neighbor and properness of the target plus equality away from `v` to exclude
source color `b` at a neighbor.

## V4 exchange bridge

`onePointRecolor_exchange_bridge` exposes, for the recolor witness, the unique
nonzero `delta` satisfying

```text
exchange delta (source v) = target v.
```

It reuses `existsUnique_nonzero_exchange_to` directly; the V4 algebra is not
duplicated.

## Singleton Kempe move and symmetry

`SingletonKempeMove G mutable source target` packages:

- the one-point witness and equality-away condition;
- the singleton `KempeReachable` characterization;
- the unique nonzero V4 exchange witness.

`onePointRecolor_singletonKempeMove` proves the required implication from
`OnePointRecolor`. The reverse projection is
`singletonKempeMove_onePointRecolor`, and symmetry is exposed by
`singletonKempeMove_symm` and `singletonKempeMove_symmetric`.

The repair-distance step relation is the abbreviation
`SingletonKempeStep G mutable`. Its symmetry theorem is
`singletonKempeStep_symmetric`.

## Repair-height corollary

`singletonKempe_repairHeight_unit_slope` is a thin application of the frozen
`repairHeight_unit_slope` theorem to `SingletonKempeStep`. It assumes a fixed
graph, one concrete singleton Kempe step, and reachability of both colorings
to an arbitrary exit predicate.

No cross-topology comparison is introduced.

## Finite regression

`KempeRepairRegression` uses `Fin 2` with the top simple graph. The source and
target are proper `TrominoState` colorings that differ only at vertex `0`,
with all vertices mutable. It proves:

- `tiny_onePoint`;
- `tiny_singleton_component`;
- `tiny_exchange_bridge`;
- `tiny_singleton_move`;
- `tiny_repair_height_unit_slope`.

The exit predicate is deliberately `True`, so the final theorem checks the
concrete repair-height interface without introducing a simulation policy.

## Axiom audit

The focused audit reports the ordinary baseline:

```text
propext, Classical.choice, Quot.sound
```

for `onePointRecolor_symm`,
`kempeReachable_singleton_of_onePointRecolor`,
`onePointRecolor_exchange_bridge`,
`onePointRecolor_singletonKempeMove`,
`singletonKempeMove_symmetric`, and
`singletonKempe_repairHeight_unit_slope`.

No new axiom declaration was added.

## Validation

Focused builds passed:

```text
lake build DkMath.Tromino.KempeRepair
lake build DkMathTest.Tromino.KempeRepairRegression
lake build DkMathTest.Tromino.KempeRepairAxiomAudit
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
```

`git diff --check` passed. The changed Lean files had no matches for
`sorry`, `admit`, a new `axiom` declaration, or `unsafe`.

The Lean 4.34 deprecation warning for the repository's existing
`Symmetric` predicate remains in the frozen core and the new symmetry
interfaces. The regression also emits a non-failing flexible-`simp_all`
linter warning in the finite coloring fixture. These are warnings only; all
focused builds completed successfully.

## Deviations and non-goals

No deviation from the requested representation or theorem boundary was
needed. No general non-singleton Kempe-chain recoloring, cross-topology
transport, child-height comparison, W9 data, sector census, Port theorem
chain, universal four-colorability, or Four Color Theorem claim was added.

## Recommendation for checkpoint 003

Integrate the concrete `SingletonKempeStep` with fixed-topology
Missing-valid/chamber semantics. Keep the existing generic reachability and
repair-height interfaces, and defer any cross-topology or universal coloring
statement.
