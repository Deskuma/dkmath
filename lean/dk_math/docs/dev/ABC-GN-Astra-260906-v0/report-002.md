# ASTRA-002 — realizability-aware profile foundation

## Result

Checkpoint 002 is implemented. The production API now distinguishes a formal
large profile from one with a nonempty exact interval fiber, exposes generic
modulus-height admissibility, and provides a realized large-profile space. The
optional realized boundary sum shell was also added. No ABC theorem, density
bound, or asymptotic estimate was attempted.

## Workspace and files

- Branch: `wip/ABC-GN-astra-260906-v0`.
- Final HEAD: `9ba7fdba30f7807d6fce946ce188d7e6099c58bb`.
- New production module: `DkMath/ABC/GNExcessRealizableProfiles.lean`.
- Public aggregator: `DkMath/ABC.lean` now imports the new module immediately
  after `GNExcessProfileOvercount`.
- No existing theorem proposition or historical rectangular profile definition
  was changed.

## Declarations added

`DkMath.ABC.GNExcessRealizableProfiles` contains:

- `GNExcessProfileRealized`, with `GNExcessProfileRealized_iff`,
  `GNExcessProfileRealized.of_point`, and
  `GNExcessProfileRealized.exists_point`.
- `GNExcessProfileHeightAdmissible` and
  `GNExcessProfileHeightAdmissible_iff`.
- `GNExcessProfileRealized.cubic_heightAdmissible`, reusing the existing
  `GNExcess_cubic_realized_modulus_le_height` theorem.
- `GNExcessRealizedLargeProfileSpace`.
- `realizedLargeProfileSpace_subset_largeProfileSpace` and
  `mem_realizedLargeProfileSpace_iff`.
- `mem_realizedLargeProfileSpace_realized` and
  `mem_realizedLargeProfileSpace_large`.
- `mem_realizedLargeProfileSpace_cubic_heightAdmissible`.
- `GNExcessTwoPrimeProfile_not_mem_realizedLargeProfileSpace`.
- Optional shell `GNExcessRealizedLargeBoundaryProfileSum` and monotonicity
  theorem `GNExcessRealizedLargeBoundaryProfileSum_le`.

The new realized space is a classical finite filter. This is necessary only for
deciding the arbitrary Prop-valued exact-event nonemptiness predicate; the
underlying event remains finite and the API is otherwise constructive in the
same sense as the surrounding profile modules.

## Main semantic bridges

For the canonical cubic family

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X,
```

the production theorem
`mem_realizedLargeProfileSpace_cubic_heightAdmissible` gives

```text
e ∈ GNExcessRealizedLargeProfileSpace Q 3 1 X
  -> GNExcessJointDepthModulus Q e ≤ 3 * (X + 1)^2.
```

Its proof extracts exact-event nonemptiness from filter membership and directly
reuses `GNExcess_cubic_realized_modulus_le_height`. The generic predicate does
not hard-code exponent three or this height.

For the known ASTRA-001 ghost profile, the theorem
`GNExcessTwoPrimeProfile_not_mem_realizedLargeProfileSpace` proves, under
`7 ∈ Q`, `13 ∈ Q`, and `1 ≤ n`,

```text
GNExcessTwoPrimeProfile Q n ∉
  GNExcessRealizedLargeProfileSpace Q 3 1 (13^n).
```

This is immediate from the existing
`GNExcessTwoPrimeProfile_event_eq_empty`; the long arithmetic emptiness proof
was not duplicated. The profile remains a member of the old rectangular large
space through `GNExcessTwoPrimeProfile_mem_large`, so the intended regression
distinction is explicit.

The optional shell sums the same nonnegative undivided boundary weight as the
historical `GNExcessLargeBoundaryProfileSum`, but only over realized members.
`GNExcessRealizedLargeBoundaryProfileSum_le` proves the immediate subset
comparison. No bound for the new shell is asserted.

## Verification

From `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessRealizableProfiles
lake build DkMath.ABC
```

Both builds completed successfully. The focused module build completed 8782
jobs; the ABC aggregator build completed 8840 jobs.

The existing repository warning
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6` (`declaration
uses sorry`) was replayed by the build and is outside the changed module. A
placeholder scan over the changed Lean module found no `sorry`, `admit`, or
`axiom`, and no reference to `abc_main_axiom`.

The principal theorem audit was run with `#print axioms` on:

```text
GNExcessProfileRealized.cubic_heightAdmissible
mem_realizedLargeProfileSpace_cubic_heightAdmissible
GNExcessTwoPrimeProfile_not_mem_realizedLargeProfileSpace
GNExcessRealizedLargeBoundaryProfileSum_le
```

Each depends only on the normal kernel boundary:

```text
propext, Classical.choice, Quot.sound
```

No new research axiom or ABC-equivalent contract was introduced.

## Remaining boundary

The realized container fixes the specific ghost-profile overcount identified in
ASTRA-001, but it does not count realized profiles or control their fibers. The
next question remains the one stated in `instruction-002.md`: determine how many
realized height-admissible large profiles can occur and what exact fiber
structure they have. This checkpoint stops before that research step.
