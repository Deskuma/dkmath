# instruction-002 — realizability-aware profile foundation

## Mission

Resume the ABC–GN implementation phase after the Astra-001 strategy review.

This is a **Codex Luna engineering checkpoint**, not an autonomous Astra
research run.

Astra-001 established that the current rectangular excess-profile container
contains infinitely many unrealizable "ghost profiles", and that the existing
raw large-boundary sum therefore cannot satisfy the intended linear bound.

The next task is to turn that discovery into a small, honest Lean API.

The goal of this checkpoint is:

> Make profile realizability and the cubic joint-height restriction explicit
> objects in the production API, then define the realized large-profile
> subspace that excludes ghost profiles by construction.

Do **not** attempt to prove ABC or a new global sum bound in this checkpoint.

---

## Repository

```text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

The branch state before this instruction was created is the post-review pause
state whose review is recorded in:

```text
review-001.md
```

Read first:

```text
README.md
ROADMAP.md
review-001.md
instruction-001.md
```

Then inspect the current production source, especially:

```text
DkMath/ABC/GNExcessActiveProfiles.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNExcessProfileOvercount.lean
DkMath/ABC/GNCubicBoundaryWeight.lean
DkMath/ABC/GNCubicOrientation.lean
```

Treat the current source as authoritative.

---

## Starting facts already in production

The following are already proved and must be reused rather than reproved.

### Exact profile fiber

```lean
GNExactExcessProfileEvent
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Finset ℕ
```

It is the exact interval fiber of points whose excess-depth profile equals the
requested profile.

### Finite profile containers

```lean
GNExcessDepthProfileSpace
GNExcessSmallProfileSpace
GNExcessLargeProfileSpace
```

The current large space is rectangular in the separate local depth
coordinates. It does not encode joint realizability.

### Joint modulus

```lean
GNExcessJointDepthModulus
```

For an excess profile, this is the product of its active prime-power depth
requests.

### Exact cubic target modulus

```lean
GNExcessJointDepthModulus_target_eq_repeatedPart
```

At an actual target point, the joint modulus is exactly the
non-exceptional repeated prime-power part.

### Astra-001 cubic height theorem

```lean
GNExcess_cubic_realized_modulus_le_height
```

Current statement:

```text
if the canonical cubic exact profile event is nonempty,
then

  GNExcessJointDepthModulus Q e <= 3 * (X + 1)^2

where

  Q = GNNonExceptionalIntervalPrimeFamily 3 1 X.
```

### Ghost-profile theorem

```lean
GNExcessTwoPrimeProfile_event_eq_empty
```

The existing two-prime 7/13 profile can belong to the current large rectangular
space while its exact realization event is empty.

### Old raw large-sum obstruction

```lean
not_exists_GNExcess_cubic_largeBoundary_linear_bound
```

This is a negative theorem about the current raw large-profile summation object.
Do not attempt to repair that old object by a stronger weight estimate.

---

## Strategic meaning

The implementation target changed after Astra-001.

Do not continue with:

```text
local depth bounds
  -> rectangular profile box
  -> sum every formal profile
```

The new intended structure is:

```text
formal finite profile space
        |
        +-- unrealized / ghost profiles
        |
        +-- realized profiles
                |
                v
        joint-height admissibility
                |
                v
        realizability-aware counting
```

This checkpoint implements only the first clean layer of that structure.

---

# Part I — introduce a generic realizability predicate

Add a small production module in the natural ABC layer.

Recommended file:

```text
DkMath/ABC/GNExcessRealizableProfiles.lean
```

Use current naming conventions if a nearby name is clearly better, but avoid a
large refactor.

Introduce a generic predicate equivalent to exact-event nonemptiness.

A recommended shape is:

```lean
def GNExcessProfileRealized
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Prop :=
  (GNExactExcessProfileEvent Q excess p b X).Nonempty
```

Prove only useful thin API around it, for example:

```text
GNExcessProfileRealized_iff
GNExcessProfileRealized.of_point
GNExcessProfileRealized.exists_point
```

Exact names are flexible.

Do not create wrappers that merely duplicate `Finset.Nonempty` without
improving downstream readability.

The purpose of this predicate is semantic:

> a profile is not merely locally allowed by the rectangular container; it is
> actually produced by at least one interval point.

---

# Part II — introduce generic height admissibility

Introduce a generic modulus-height predicate.

Recommended shape:

```lean
def GNExcessProfileHeightAdmissible
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (H : ℕ) : Prop :=
  GNExcessJointDepthModulus Q excess ≤ H
```

If a more argument-efficient order fits existing DkMath style, use it.

This definition must remain generic. It should not hard-code cubic exponent 3
or the specific height `3 * (X + 1)^2`.

Then expose the canonical cubic specialization as a theorem or small predicate.

The essential theorem is:

```text
canonical cubic realized profile
  ->
height-admissible with H = 3 * (X + 1)^2.
```

This theorem should be a direct reuse / repackaging of:

```lean
GNExcess_cubic_realized_modulus_le_height
```

Do not reprove the arithmetic unless the existing theorem signature makes a
very small refactor clearly preferable.

The desired semantic bridge is:

```text
realized
  -> joint modulus is globally compatible with cubic height.
```

---

# Part III — define the realized large-profile space

Define a finite subspace of the existing large-profile container that filters
by actual realizability.

Recommended shape:

```lean
def GNExcessRealizedLargeProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) :=
  (GNExcessLargeProfileSpace Q p b X).filter
    (fun excess =>
      GNExcessProfileRealized Q excess p b X)
```

Because the realization event is finite, decidability should be available.
Use the simplest current Lean formulation; avoid introducing classical
machinery beyond what the surrounding profile modules already use.

Prove the minimal set-theoretic API:

```text
realizedLargeProfileSpace_subset_largeProfileSpace

mem_realizedLargeProfileSpace_iff

mem_realizedLargeProfileSpace_realized

mem_realizedLargeProfileSpace_large
```

Names may follow nearby DkMath conventions.

Do not build a facade hierarchy around these lemmas.

---

# Part IV — prove the cubic height property on the realized space

For the canonical cubic prime family

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X
```

prove that every member of the realized large-profile space satisfies the Astra
joint-height restriction:

```text
e ∈ GNExcessRealizedLargeProfileSpace Q 3 1 X
  ->
GNExcessJointDepthModulus Q e ≤ 3 * (X + 1)^2.
```

Prefer a theorem phrased through the generic
`GNExcessProfileHeightAdmissible` predicate if that makes the API cleaner.

This should be a short consumer theorem whose proof extracts realization from
membership and invokes:

```lean
GNExcess_cubic_realized_modulus_le_height
```

This theorem is the main positive deliverable of checkpoint 002.

---

# Part V — certify that the Astra ghost profile is excluded

Reuse the existing two-prime family to prove that the known ghost profile does
not belong to the realized large-profile space.

The core result should say, under the existing hypotheses on `Q`, `n`:

```text
GNExcessTwoPrimeProfile Q n
  ∉ GNExcessRealizedLargeProfileSpace Q 3 1 (13^n).
```

The proof should be immediate from:

```lean
GNExcessTwoPrimeProfile_event_eq_empty
```

plus the new membership definition.

This theorem is important because it demonstrates that the new container
removes exactly the pathology identified by Astra-001.

Do not re-run the long arithmetic proof of event emptiness.

---

# Optional Part VI — realized large-boundary sum shell

Only if Parts I–V compile cleanly and the implementation remains small, define
the honest replacement summation shell:

```lean
noncomputable def GNExcessRealizedLargeBoundaryProfileSum
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessRealizedLargeProfileSpace Q p b X,
    (((p - 1) ^
        (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) *
      Real.exp (t * GNExcessActiveProfileMass Q excess)
```

If added, prove only the immediate monotonic comparison:

```text
GNExcessRealizedLargeBoundaryProfileSum ...
  ≤ GNExcessLargeBoundaryProfileSum ...
```

using nonnegativity and subset inclusion.

Do **not** attempt any asymptotic, linear, sublinear, or ABC-relevant bound for
the new sum in checkpoint 002.

If adding this definition causes import complexity or proof-engineering drag,
stop after Part V. It is explicitly optional.

---

## Public import

If a new module is added, connect it to the ABC public aggregator only after
the focused module build succeeds.

Recommended import ordering is after the existing profile / overcount layer,
with no unrelated rearrangement.

Do not change the public proposition of existing theorems.

---

## Regression / sanity checks

Preserve the Astra-001 distinction:

```text
formal profile membership
  != actual realizability.
```

The existing two-prime profile should remain:

```text
member of the old large rectangular space
not member of the new realized large space.
```

This is the most useful regression for the new API.

If convenient, add a theorem combining these two facts, but do not add
numerical examples merely for display.

---

## Hard boundaries

- Do not use `abc_main_axiom`.
- Do not use `sorry`, `admit`, or a new axiom.
- Do not claim that the new realized sum is bounded.
- Do not claim ABC, an ABC-equivalent joint contract, or a new density theorem.
- Do not delete or weaken the negative theorem
  `not_exists_GNExcess_cubic_largeBoundary_linear_bound`.
- Do not redefine the old `GNExcessLargeProfileSpace`; preserve it as the
  historical rectangular majorant object.
- Do not silently change the meaning of
  `GNExcessLargeBoundaryProfileSum`.
- Do not generalize the cubic height theorem beyond what current source
  actually proves.
- Avoid large refactors of `GNExcessActiveProfiles.lean`.
- Keep this checkpoint implementation-sized for Codex Luna.

---

## Verification

At minimum run focused builds for the new module and the ABC aggregator.

Suggested commands from `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessRealizableProfiles
lake build DkMath.ABC
```

If the final module name differs, adjust the focused build accordingly.

Also perform a no-placeholder check on changed Lean files.

For the main new positive theorem and ghost-exclusion theorem, inspect their
axiom dependencies with the normal Lean audit mechanism used by this project.

Expected trust boundary is the normal Mathlib / Lean kernel boundary only.

---

## Deliverable

Implement the checkpoint and create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-002.md
```

The report should include:

1. final branch HEAD,
2. files changed,
3. exact declarations added,
4. focused build results,
5. ABC aggregator build result,
6. no-sorry / placeholder result,
7. axiom audit for the principal new theorems,
8. confirmation that the 7/13 ghost profile is excluded from the new realized
   container,
9. whether the optional realized large-boundary sum shell was added,
10. any Lean API friction or naming changes from this instruction.

If the requested generic definitions turn out to conflict with existing API,
prefer the smallest mathematically equivalent implementation and explain the
difference in `report-002.md`.

---

## Stop condition

Stop after the realizability-aware foundation is implemented and verified.

Do not continue autonomously into a global counting theorem.

The next research question, after checkpoint 002, will be:

```text
How many realized height-admissible large profiles can occur,
and what exact fiber structure do they have?
```

That question may require a new design/review step before further
implementation.

Checkpoint 002 succeeds when the codebase can express, in production Lean:

```text
formal large profile
        !=
realized large profile

and

realized canonical cubic profile
        ->
joint-height admissible.
```
