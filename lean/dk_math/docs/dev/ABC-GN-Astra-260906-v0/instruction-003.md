# instruction-003 — exact realized-profile fiber partition

## Mission

Continue the implementation phase after checkpoint 002.

This checkpoint is **LUNA-003**: a Codex Luna engineering task.

Checkpoint 002 introduced the semantic distinction

```text
formal profile
  !=
realized profile
```

and constructed a realized large-profile container.

The next task is to expose the exact finite map underlying realizability:

```text
a in [0, X]
  |-> GNExcessDepthProfileAt Q p b a.
```

The goal is to prove that realized profiles are exactly the image of this map
and that the exact profile events form a disjoint partition of the interval.

This checkpoint should move from

```text
realized profile
```

to

```text
actual fiber
  ->
actual interval points.
```

Do not attempt a new global ABC estimate, asymptotic counting theorem, or
density theorem in this checkpoint.

---

## Repository

```text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

Starting implementation HEAD:

```text
b7a3c3de882ac4980d3b1fbe6f4af493badfe361
impl: 002 — realizability-aware profile foundation
```

Read first:

```text
README.md
ROADMAP.md
review-001.md
report-002.md
instruction-002.md
```

Then inspect current source, especially:

```text
DkMath/ABC/GNExcessActiveProfiles.lean
DkMath/ABC/GNExcessRealizableProfiles.lean
DkMath/ABC/GNExcessProfileOvercount.lean
```

Treat current production source as authoritative.

---

## Documentation cleanup

Before or during this checkpoint, fix the small historical record mismatch in
`report-002.md`.

It currently records the instruction commit as the final HEAD.

Update it to record the actual checkpoint-002 implementation HEAD:

```text
b7a3c3de882ac4980d3b1fbe6f4af493badfe361
```

Do not rewrite the mathematical content of `report-002.md`.

For checkpoint naming from here onward, use:

```text
LUNA-003
LUNA-004
...
```

for ordinary Codex Luna implementation checkpoints.

Do not reuse the ROADMAP research label `ASTRA-003` for this checkpoint.

---

# Starting API

The following production declarations already exist.

## Pointwise profile

```lean
GNExcessDepthProfileAt
    (Q : Finset ℕ) (p b a : ℕ) :
    ∀ q ∈ Q, ℕ
```

## Exact fiber

```lean
GNExactExcessProfileEvent
    (Q : Finset ℕ)
    (excess : ∀ q ∈ Q, ℕ)
    (p b X : ℕ) : Finset ℕ
```

By definition this is:

```text
a in Icc 0 X
with
GNExcessDepthProfileAt Q p b a = excess.
```

## Semantic realizability

```lean
GNExcessProfileRealized
    Q excess p b X
```

and

```lean
GNExcessProfileRealized_iff
```

identify realizability with nonempty exact fiber.

## Formal finite profile space

```lean
GNExcessDepthProfileSpace
```

and

```lean
GNExcessDepthProfileAt_mem_space
```

show that actual interval points produce formal profiles when the existing
positivity hypotheses hold.

## Realized large profile space

```lean
GNExcessRealizedLargeProfileSpace
```

already filters the historical large-profile space by exact realizability.

Do not replace or redefine these objects.

---

# Part I — define the exact realized profile image

Add a new production module.

Recommended file:

```text
DkMath/ABC/GNExcessRealizedFibers.lean
```

A nearby name is acceptable if it better matches repository style.

Define the finite image of the actual interval map.

Recommended shape:

```lean
noncomputable def GNExcessRealizedProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) := by
  classical
  exact (Finset.Icc 0 X).image
    (fun a => GNExcessDepthProfileAt Q p b a)
```

The exact implementation may use a local helper function if elaboration is
cleaner.

This object is conceptually different from the old rectangular profile space:

```text
GNExcessDepthProfileSpace
  = formal coordinate box

GNExcessRealizedProfileSpace
  = exact image of actual interval points
```

---

# Part II — characterize membership exactly

Prove the central equivalence:

```text
excess ∈ GNExcessRealizedProfileSpace Q p b X
  <->
GNExcessProfileRealized Q excess p b X.
```

Recommended theorem name:

```lean
mem_GNExcessRealizedProfileSpace_iff
```

or a nearby repository-consistent name.

The proof should come directly from:

- `Finset.mem_image`,
- the definition of `GNExactExcessProfileEvent`,
- `GNExcessProfileRealized_iff`.

Do not route through the large-profile space.

Also provide thin consumer lemmas if useful:

```text
point_profile_mem_realizedProfileSpace

realizedProfileSpace_exists_point
```

Avoid redundant wrappers.

---

# Part III — connect exact image to the formal finite space

Under the existing positivity hypothesis needed by
`GNExcessDepthProfileAt_mem_space`, prove:

```text
GNExcessRealizedProfileSpace Q p b X
  ⊆
GNExcessDepthProfileSpace Q p b X.
```

This should be an immediate consequence of the fact that every image witness
lies in `Icc 0 X`.

Recommended theorem shape:

```lean
GNExcessRealizedProfileSpace_subset_depthProfileSpace
    (hb : 0 < b) : ...
```

This theorem documents that:

```text
actual image
  ⊆
formal rectangular container.
```

Do not prove the converse; it is false in general and Astra-001 supplied a
counterexample mechanism.

---

# Part IV — prove exact fiber disjointness

For two distinct profiles, prove their exact interval fibers are disjoint.

Target theorem:

```text
e₁ ≠ e₂
  ->
Disjoint
  (GNExactExcessProfileEvent Q e₁ p b X)
  (GNExactExcessProfileEvent Q e₂ p b X).
```

Recommended name:

```lean
GNExactExcessProfileEvent_disjoint
```

The proof should be elementary:

a common point would have pointwise profile equal to both `e₁` and `e₂`.

This theorem is important. It makes the exact fibers a genuine partition, not
merely a family of subsets.

Do not introduce valuation arithmetic here.

---

# Part V — prove interval coverage by exact fibers

Prove that every interval point belongs to the exact event of its own profile.

Recommended theorem:

```lean
mem_GNExactExcessProfileEvent_profileAt
    {a : ℕ}
    (ha : a ∈ Finset.Icc 0 X) :
    a ∈ GNExactExcessProfileEvent Q
      (GNExcessDepthProfileAt Q p b a) p b X
```

Then prove an exact union / coverage theorem over the realized profile space.

Desired mathematical statement:

```text
union over e in GNExcessRealizedProfileSpace Q p b X
  of GNExactExcessProfileEvent Q e p b X

=
Finset.Icc 0 X.
```

Use whichever standard `Finset` union construction makes the Lean proof
smallest and clearest.

Possible implementations include `Finset.biUnion` or an equivalent finite
union expression.

Do not create a complicated custom union data structure.

This exact coverage theorem plus Part IV is the main deliverable of LUNA-003.

---

# Part VI — cardinal consequences

Once the image theorem is available, prove the cheap and useful bound:

```text
(GNExcessRealizedProfileSpace Q p b X).card ≤ X + 1.
```

Use the image-cardinality bound and the exact cardinality of
`Finset.Icc 0 X`.

This is a structural sanity theorem only.

Do not present it as sufficient for the large-boundary problem.

The following crude multiplication is explicitly **not** a target:

```text
number of profiles <= X+1
times
one-profile weight <= O(X^(3/4))
```

because that would only give a crude `O(X^(7/4))` scale.

---

# Optional Part VII — exact cardinal partition

Only if Parts I–VI are clean, prove:

```text
sum over realized profiles e
  of (GNExactExcessProfileEvent Q e p b X).card
=
X + 1.
```

This is stronger than the image-cardinality bound because it accounts for the
sizes of all exact fibers.

Use the disjointness and coverage theorems rather than reproving the statement
with ad hoc arithmetic.

If the generic `Finset` partition API becomes disproportionately expensive,
stop after Part VI and record the friction in `report-003.md`.

---

# Optional Part VIII — exact weighted fiber reindex

Only attempt this if the preceding partition API is already stable and the
proof is short.

The intended identity is conceptually:

```text
sum a in Icc 0 X,
  exp (t * GNExcessMassAt Q p b a)

=

sum e in GNExcessRealizedProfileSpace Q p b X,
  card (GNExactExcessProfileEvent Q e p b X)
    * exp (t * GNExcessActiveProfileMass Q e).
```

Use the existing theorem:

```lean
GNExcessMassAt_eq_activeProfileMass
```

on each exact fiber.

The exact cast placement may be chosen to match existing real-sum APIs.

This identity is valuable because it rewrites an actual pointwise moment as a
sum over actual fibers.

However, it is optional.

Do not spend the checkpoint rebuilding a generic measure-theory or partition
library if Mathlib's finite-sum API makes this awkward.

---

# Relation to the realized large-profile space

If useful and inexpensive, prove the exact relation:

```text
GNExcessRealizedLargeProfileSpace Q p b X
=
(GNExcessRealizedProfileSpace Q p b X).filter
  (fun excess =>
    X + 1 < GNExcessJointDepthModulus Q excess).
```

or the corresponding membership equivalence.

This should be a semantic cleanup theorem, not a refactor.

Do not redefine the checkpoint-002 object.

---

# What this checkpoint is NOT

Do not attempt any of the following:

- a linear bound for `GNExcessRealizedLargeBoundaryProfileSum`,
- an asymptotic count of realized profiles,
- a new Euler product,
- a new CRT density theorem,
- an ABC-quality coupling,
- a paired-orientation global theorem,
- a descent,
- any use of `abc_main_axiom`.

The purpose is exact finite bookkeeping of **actual fibers**, not a new
research theorem.

---

## Public import

If a new module is added, import it from `DkMath.ABC` immediately after
`GNExcessRealizableProfiles` unless current dependency order requires a
nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

```bash
lake build DkMath.ABC.GNExcessRealizedFibers
lake build DkMath.ABC
```

Adjust the focused module name if a different production filename is chosen.

Also:

- scan changed Lean files for `sorry`, `admit`, new `axiom`,
- confirm no reference to `abc_main_axiom`,
- audit axioms for the central image/membership theorem,
  disjointness theorem, and coverage theorem.

Expected dependency boundary:

```text
propext
Classical.choice
Quot.sound
```

or a subset thereof.

Existing unrelated repository `sorry` warnings may remain, but report them
separately.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-003.md
```

Title it as a Luna checkpoint, for example:

```text
# LUNA-003 — exact realized-profile fiber partition
```

Include:

1. final branch HEAD,
2. files changed,
3. exact declarations added,
4. focused build result,
5. ABC aggregator build result,
6. no-placeholder / no-new-axiom result,
7. axiom audit for principal theorems,
8. exact membership/image characterization,
9. exact disjointness result,
10. interval coverage result,
11. realized-profile cardinal bound,
12. whether optional exact cardinal partition was completed,
13. whether optional weighted fiber reindex was completed,
14. any Mathlib `Finset` API friction,
15. the exact next unresolved implementation boundary.

Update README / ROADMAP minimally to mark LUNA-003 complete if the checkpoint
succeeds.

---

## Stop condition

Stop once the exact realized-profile image and fiber partition are production
Lean and verified.

Do not autonomously continue into a counting estimate.

The next decision point should be based on what the exact partition exposes.

The likely next research/implementation question is:

```text
Given the exact partition of actual interval points into realized profiles,
what additional structure controls the sizes of the realized large fibers?
```

LUNA-003 succeeds when DkMath can state and prove, without approximation:

```text
realized profiles
  = image of actual interval points

distinct profiles
  -> disjoint exact fibers

union of exact realized fibers
  = the entire interval.
```
