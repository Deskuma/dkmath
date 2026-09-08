# instruction-004 — ghost-free realized moment bridge

## Mission

Continue the ABC–GN implementation phase after LUNA-003.

This checkpoint is **LUNA-004**.

LUNA-003 proved that the exact realized fibers form a disjoint partition of
the interval. The next task is to use that exact partition to rebuild the
exponential-moment bridge without paying boundary weight to unrealized ghost
profiles.

The main target is:

```text
actual pointwise exponential moment
  ->
exact realized fibers
  ->
small realized fibers + large realized fibers
  ->
old small-density majorant + realized large-boundary majorant
```

The large contribution must use:

```lean
GNExcessRealizedLargeBoundaryProfileSum
```

not the historical raw:

```lean
GNExcessLargeBoundaryProfileSum
```

Do not attempt to bound the new realized large-boundary sum in this
checkpoint.

---

## Repository

```text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

Read first:

```text
README.md
ROADMAP.md
review-001.md
report-002.md
report-003.md
instruction-003.md
```

Then inspect current production source, especially:

```text
DkMath/ABC/GNExcessActiveProfiles.lean
DkMath/ABC/GNExcessRealizableProfiles.lean
DkMath/ABC/GNExcessRealizedFibers.lean
```

Treat current source as authoritative.

---

## Reporting policy

Do **not** record branch HEAD hashes or commit hashes in `report-004.md`.

Git already records that information, and the human-facing report should focus
on mathematical / Lean content rather than duplicate repository metadata.

Do not spend work updating historical reports merely to synchronize commit
hashes.

---

# Starting facts already in production

The following exact finite structure is complete.

## Exact realized profile image

```lean
GNExcessRealizedProfileSpace
```

with

```lean
mem_GNExcessRealizedProfileSpace_iff
```

showing:

```text
profile is in realized image
  <->
its exact interval fiber is nonempty.
```

## Exact fibers

```lean
GNExactExcessProfileEvent
```

with:

```lean
GNExactExcessProfileEvent_disjoint
biUnion_GNExactExcessProfileEvent_eq_Icc
sum_card_GNExactExcessProfileEvent_eq_interval
```

Hence the realized fibers form an exact disjoint partition of
`Finset.Icc 0 X`.

## Pointwise/profile mass identity

```lean
GNExcessMassAt_eq_activeProfileMass
```

On an exact fiber, the pointwise excess mass is exactly the profile mass.

## Existing small / large fiber estimates

For small modulus:

```lean
card_GNExactExcessProfileEvent_le_smallDensity
```

For large modulus:

```lean
card_GNExactExcessProfileEvent_le_largeBoundary
```

## Existing majorants

Small:

```lean
GNExcessSmallDensityProfileSum
GNExcessFiniteEulerDensity
```

Historical raw large:

```lean
GNExcessLargeBoundaryProfileSum
```

Realized large:

```lean
GNExcessRealizedLargeBoundaryProfileSum
```

The realized large sum is already known to satisfy:

```lean
GNExcessRealizedLargeBoundaryProfileSum_le
```

but no asymptotic bound for it is known.

---

# Part I — exact weighted fiber reindex

Add a production module in the natural ABC layer.

Recommended file:

```text
DkMath/ABC/GNExcessRealizedMoment.lean
```

A nearby name is acceptable if it fits repository style better.

First prove the exact weighted reindex deferred from LUNA-003.

Target identity:

```text
sum a in Finset.Icc 0 X,
  Real.exp (t * GNExcessMassAt Q p b a)

=

sum excess in GNExcessRealizedProfileSpace Q p b X,
  ((GNExactExcessProfileEvent Q excess p b X).card : ℝ) *
    Real.exp (t * GNExcessActiveProfileMass Q excess).
```

Recommended theorem name:

```lean
exp_GNExcessMassAt_sum_eq_realizedFiberSum
```

The proof should use the exact realized partition from LUNA-003 and:

```lean
GNExcessMassAt_eq_activeProfileMass
```

Do not reindex through `GNExcessDepthProfileSpace`.

The important semantic fact is:

> the weighted sum is rewritten over profiles that actually occur, not over the
> rectangular formal container.

If the most direct proof is a specialized use of
`Finset.sum_fiberwise_of_maps_to`, that is acceptable, provided the final
index set is the exact realized image.

---

# Part II — realized small-profile space

If useful for a clean proof, introduce the realized small-profile counterpart
to the existing realized large space.

Recommended shape:

```lean
noncomputable def GNExcessRealizedSmallProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) := by
  classical
  exact (GNExcessRealizedProfileSpace Q p b X).filter
    (fun excess =>
      GNExcessJointDepthModulus Q excess ≤ X + 1)
```

Then prove minimal API:

```text
mem_realizedSmallProfileSpace_iff
realizedSmallProfileSpace_subset_smallProfileSpace
```

Also expose the relation between the LUNA-002 large space and the LUNA-003
exact image, either as equality or membership equivalence:

```text
excess ∈ GNExcessRealizedLargeProfileSpace Q p b X
  <->
excess ∈ GNExcessRealizedProfileSpace Q p b X
  and
X + 1 < GNExcessJointDepthModulus Q excess.
```

Recommended theorem:

```lean
mem_realizedLargeProfileSpace_iff_realized_and_large
```

Use an equality of finite sets instead if that is simpler.

Do not redefine `GNExcessRealizedLargeProfileSpace`.

---

# Part III — exact realized small/large split

Prove that every realized profile is exactly one of small or large according
to the modulus comparison.

The underlying arithmetic dichotomy is simply:

```text
M ≤ X + 1
or
X + 1 < M.
```

Expose whichever finite-set theorem is simplest and useful:

```text
realized profile space
  = realized small union realized large
```

with disjointness, or an equivalent sum-splitting theorem.

Do not build a custom partition structure.

This is a finite bookkeeping theorem only.

---

# Part IV — ghost-free moment bound

This is the main theorem of LUNA-004.

Prove the realized replacement for the historical theorem
`exp_GNExcessMassAt_sum_le_small_add_large`.

Target shape:

```lean
theorem exp_GNExcessMassAt_sum_le_small_add_realizedLarge
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t +
        GNExcessRealizedLargeBoundaryProfileSum Q p b X t
```

Exact theorem name may vary slightly.

Proof strategy:

1. rewrite the point sum using the exact realized-fiber identity from Part I,
2. split realized profiles into small and large,
3. for a small realized fiber use
   `card_GNExactExcessProfileEvent_le_smallDensity`,
4. enlarge the realized small contribution to the existing formal
   `GNExcessSmallDensityProfileSum`,
5. for a large realized fiber use
   `card_GNExactExcessProfileEvent_le_largeBoundary`,
6. identify the resulting large sum exactly with
   `GNExcessRealizedLargeBoundaryProfileSum`.

The proof must never sum boundary weight over an unrealized profile.

This theorem is the main success criterion.

---

# Part V — finite Euler variant

After Part IV, prove the direct consumer variant:

```lean
theorem exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge ...
```

with conclusion:

```text
pointwise moment
  ≤
2 * (X + 1) * GNExcessFiniteEulerDensity
  +
GNExcessRealizedLargeBoundaryProfileSum.
```

Reuse:

```lean
GNExcessSmallDensityProfileSum_le_finiteEulerDensity
```

Do not redo the Euler-product proof.

This theorem should be a short consequence of Part IV.

---

# Part VI — preserve the historical theorem

Do not delete, rename, weaken, or silently change:

```lean
exp_GNExcessMassAt_sum_le_small_add_large
exp_GNExcessMassAt_sum_le_finiteEuler_add_large
```

They are historically valid majorant theorems, although their large term is
now known to be structurally loose.

The new realized theorems should live beside them and make the distinction
explicit.

If useful, add docstrings saying:

```text
historical raw large majorant
vs
realizability-aware large majorant.
```

Do not refactor the old proof unless a tiny reuse extraction is clearly
beneficial and low-risk.

---

# Part VII — canonical cubic specialization

Only if Parts I–V compile cleanly, add a small canonical cubic corollary using:

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X.
```

The corollary should merely instantiate the new ghost-free moment theorem.

Do not attempt to use the cubic height bound or the 3/8 target bound to derive a
new asymptotic estimate here.

If the hypotheses `hQprime`, `hQp`, `hQb` are already available through
existing canonical-family lemmas, reuse them.

If assembling those hypotheses creates disproportionate plumbing, skip this
optional specialization and report the API friction.

---

# What this checkpoint is NOT

Do not attempt:

- a bound for `GNExcessRealizedLargeBoundaryProfileSum`,
- a linear / sublinear large-boundary theorem,
- a new profile-count asymptotic,
- a new CRT density theorem,
- a paired-orientation theorem,
- an `abcEpsilon` or quality coupling,
- a descent,
- any theorem using `abc_main_axiom`.

The point of LUNA-004 is to repair the analytical bridge so that the actual
moment no longer depends on the refuted raw large-profile sum.

---

## Public import

If a new module is added, import it from `DkMath.ABC` immediately after
`GNExcessRealizedFibers` unless current dependency order requires a nearby
placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

```bash
lake build DkMath.ABC.GNExcessRealizedMoment
lake build DkMath.ABC
```

Adjust the focused module name if needed.

Also:

- scan changed Lean files for `sorry`, `admit`, new `axiom`,
- confirm no reference to `abc_main_axiom`,
- audit axioms for:
  - the exact weighted realized-fiber identity,
  - the ghost-free small + realized-large theorem,
  - the finite-Euler + realized-large theorem.

Expected dependency boundary:

```text
propext
Classical.choice
Quot.sound
```

or a subset thereof.

Existing unrelated repository warnings may remain and should be reported
separately.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-004.md
```

Title:

```text
# LUNA-004 — ghost-free realized moment bridge
```

Do **not** include branch HEAD hashes or commit hashes.

Report only information useful to a human reader:

1. files changed,
2. declarations added,
3. exact weighted realized-fiber identity,
4. realized small/large split API added,
5. new ghost-free moment theorem,
6. finite Euler variant,
7. whether a canonical cubic specialization was added,
8. focused build result,
9. ABC aggregator build result,
10. no-placeholder / no-new-axiom result,
11. axiom audit of principal theorems,
12. any Lean / Finset API friction,
13. exact remaining mathematical blocker.

Update README / ROADMAP minimally if the checkpoint succeeds.

---

## Stop condition

Stop once the actual exponential moment has been reconnected to:

```text
small-density contribution
+
realized large-boundary contribution.
```

Do not continue autonomously into a bound for the realized large term.

The next decision point is mathematical rather than bookkeeping:

```text
What structure controls

  fiber.card
    ×
  realized large-profile weight

for the profiles that actually occur?
```

LUNA-004 succeeds when the old ghost-contaminated large term is no longer
needed in the strongest production moment bridge.
