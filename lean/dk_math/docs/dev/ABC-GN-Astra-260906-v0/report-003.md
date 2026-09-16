# LUNA-003 — exact realized-profile fiber partition

## Result

LUNA-003 is implemented. The production API now identifies realized profiles
with the finite image of the actual interval map, proves that distinct exact
fibers are disjoint, and proves that the realized fibers cover the whole
interval `[0, X]`. The optional exact cardinal partition was also completed.
No global ABC estimate, asymptotic counting theorem, or density theorem was
attempted.

## Workspace and files

- Branch: `wip/ABC-GN-astra-260906-v0`.
- Branch HEAD at verification: `53cea136a2a55c8f6cac1a70d85b9097ad48663d`.
- New production module: `DkMath/ABC/GNExcessRealizedFibers.lean`.
- Public aggregator: `DkMath/ABC.lean` now imports the new module immediately
  after `GNExcessRealizableProfiles`.
- Documentation: `README.md`, `ROADMAP.md`, and this report were updated.
- The historical HEAD in `report-002.md` was corrected to
  `b7a3c3de882ac4980d3b1fbe6f4af493badfe361` as requested.
- Existing profile definitions and prior theorem propositions were not
  changed.

## Declarations added

`DkMath.ABC.GNExcessRealizedFibers` contains:

- `GNExcessRealizedProfileSpace`, the image of `Finset.Icc 0 X` under
  `GNExcessDepthProfileAt`.
- `mem_GNExcessRealizedProfileSpace_iff`, identifying image membership with
  `GNExcessProfileRealized`.
- `point_profile_mem_realizedProfileSpace` and
  `realizedProfileSpace_exists_point`.
- `GNExcessRealizedProfileSpace_subset_depthProfileSpace` under `0 < b`.
- `GNExactExcessProfileEvent_disjoint` for distinct profiles.
- `mem_GNExactExcessProfileEvent_profileAt`.
- `biUnion_GNExactExcessProfileEvent_eq_Icc`, the exact interval coverage
  theorem.
- `card_GNExcessRealizedProfileSpace_le_interval`.
- `sum_card_GNExactExcessProfileEvent_eq_interval`, the exact cardinal
  partition.

## Exact finite semantics

For every profile `excess`,

```text
excess ∈ GNExcessRealizedProfileSpace Q p b X
  ↔ GNExcessProfileRealized Q excess p b X.
```

For distinct profiles, their exact events are disjoint. Moreover,

```text
(GNExcessRealizedProfileSpace Q p b X).biUnion
  (fun excess => GNExactExcessProfileEvent Q excess p b X)
  = Finset.Icc 0 X.
```

Consequently,

```text
(GNExcessRealizedProfileSpace Q p b X).card ≤ X + 1
```

and the stronger fiber-cardinality identity is proved:

```text
∑ excess ∈ GNExcessRealizedProfileSpace Q p b X,
  (GNExactExcessProfileEvent Q excess p b X).card = X + 1.
```

The weighted fiber reindex identity from the instruction was not attempted;
it is not needed for the exact partition checkpoint.

## Verification

From `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessRealizedFibers
lake build DkMath.ABC
```

Both builds completed successfully. The focused module build completed 8783
jobs, and the ABC aggregator build completed 8841 jobs.

A placeholder scan over the changed Lean module found no `sorry`, `admit`, or
`axiom`, and no reference to `abc_main_axiom`. The existing repository warning
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6` (`declaration
uses sorry`) remains outside the changed module.

The principal image, disjointness, coverage, and cardinal-partition theorems
were audited with `#print axioms`; each depends only on

```text
propext, Classical.choice, Quot.sound
```

No new research axiom or ABC-equivalent contract was introduced.

## API friction and boundary

No material `Finset` API obstruction occurred. The image characterization and
coverage use `Finset.mem_image` and `Finset.mem_biUnion`; the cardinal identity
uses `Finset.card_biUnion` with the proved pairwise disjointness.

The exact partition fixes the finite bookkeeping boundary but does not control
the sizes of individual realized large fibers or their aggregate boundary
weight. The next unresolved implementation question is to determine what
additional structure bounds those realized large fibers. This checkpoint stops
there.
