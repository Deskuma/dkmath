# instruction-005 — cubic 3/8 realized-fiber transfer

## Mission

Continue the ABC–GN implementation phase after LUNA-004.

This checkpoint is **LUNA-005**.

LUNA-004 removed ghost profiles from the strongest production moment bridge.
The remaining realized large term is still written using the CRT root-address
charge:

```text
rootAddressCharge(e)
  * exp (t * activeProfileMass(e)).
```

Astra already proved the cubic target theorem at `t = 3/8`:

```text
target root-address weight
  <=
repeatedPart^(3/8).
```

The purpose of LUNA-005 is to transport that theorem from a concrete target
point to an arbitrary **realized canonical cubic large profile**, then sum it.

The desired reduction is:

```text
realized cubic large profile e
        |
        v
choose actual witness a in its exact fiber
        |
        v
root-address weight at e
        <= repeatedPart(3,a,1)^(3/8)
        |
        v
repeatedPart(3,a,1)
        = joint modulus M(e)
        |
        v
profile boundary weight
        <= M(e)^(3/8)
```

Then:

```text
GNExcessRealizedLargeBoundaryProfileSum(..., 3/8)
  <=
sum over realized large profiles e of M(e)^(3/8).
```

Do not attempt to bound that final modulus sum in this checkpoint.

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
report-004.md
instruction-004.md
```

Then inspect current production source, especially:

```text
DkMath/ABC/GNCubicBoundaryWeight.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNExcessRealizableProfiles.lean
DkMath/ABC/GNExcessRealizedFibers.lean
DkMath/ABC/GNExcessRealizedMoment.lean
```

Treat current source as authoritative.

---

## Reporting policy

Do **not** record branch HEAD hashes or commit hashes in `report-005.md`.

Git is the source of truth for repository history. The report should contain
only information useful for mathematical and Lean review.

---

# Starting facts already in production

## Canonical cubic target weight

```lean
GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths
```

For a positive target point `a`, positive boundary `b), interval membership,
and coprimality:

```text
GNExcessRootAddressCharge(target profile)
  * exp ((3/8) * target profile mass)
<=
GNNonExceptionalRepeatedPart 3 a b ^ (3/8).
```

## Target modulus identity

```lean
GNExcessJointDepthModulus_target_eq_repeatedPart
```

For a canonical target profile:

```text
joint modulus(target profile)
=
GNNonExceptionalRepeatedPart.
```

## Realized large space

```lean
GNExcessRealizedLargeProfileSpace
```

and:

```lean
mem_realizedLargeProfileSpace_iff_realized_and_large
mem_realizedLargeProfileSpace_realized
```

provide an actual exact-fiber witness for every realized large profile.

## Canonical cubic height

```lean
mem_realizedLargeProfileSpace_cubic_heightAdmissible
```

gives:

```text
M(e) <= 3 * (X + 1)^2
```

for every realized canonical cubic large profile.

This height theorem is available for a final diagnostic corollary, but it does
not by itself solve the aggregate problem.

## Ghost-free moment bridge

```lean
exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic
```

already gives:

```text
actual cubic pointwise moment
<=
2 * (X + 1) * finite Euler density
+
realized large-boundary sum.
```

LUNA-005 should replace the last term at `t = 3/8` by a realized modulus
moment.

---

# Part I — positive witness for a realized cubic large profile

The Astra target theorem requires `0 < a`.

A realized profile formally supplies only:

```text
a ∈ Finset.Icc 0 X.
```

For the canonical cubic family with `b = 1`, prove that a **large** realized
profile cannot be realized at `a = 0`.

Recommended helper theorem shape:

```lean
theorem exists_positive_point_of_mem_realizedLarge_cubic
    {X : ℕ}
    {excess : ∀ q ∈ GNNonExceptionalIntervalPrimeFamily 3 1 X, ℕ}
    (h : excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X) :
    ∃ a : ℕ,
      0 < a ∧
      a ∈ GNExactExcessProfileEvent
        (GNNonExceptionalIntervalPrimeFamily 3 1 X)
        excess 3 1 X
```

Exact name is flexible.

Expected strategy:

1. extract a realization witness,
2. if `a = 0`, use the target modulus identity at zero,
3. evaluate the canonical cubic zero target,
4. contradict the large-modulus condition.

Keep the proof local and elementary.

Do not introduce a general nonzero-witness framework unless current APIs make
that genuinely simpler.

If a small helper theorem such as

```text
canonical cubic target modulus at a = 0 is 1
```

makes the proof clean, add it with an explicit docstring.

---

# Part II — profile-level cubic 3/8 boundary theorem

Add a new production module.

Recommended file:

```text
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
```

A nearby name is acceptable if it better matches repository style.

For:

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X
```

prove the central profile theorem:

```text
e ∈ GNExcessRealizedLargeProfileSpace Q 3 1 X
  ->
GNExcessRootAddressCharge Q 3 e
  * exp ((3/8) * GNExcessActiveProfileMass Q e)
<=
(GNExcessJointDepthModulus Q e : ℝ) ^ (3/8).
```

Recommended theorem name:

```lean
GNExcess_cubic_realizedLarge_boundaryWeight_le_modulus_three_eighths
```

or a repository-consistent variant.

Proof strategy:

1. obtain a positive exact-fiber witness from Part I,
2. extract its interval membership and profile equality,
3. use `Nat.Coprime a 1`,
4. invoke
   `GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths`,
5. rewrite the target profile to `e`,
6. rewrite repeated part to the joint modulus using
   `GNExcessJointDepthModulus_target_eq_repeatedPart`.

Do not reprove the cubic prime-lower-bound or logarithmic argument from
`GNCubicBoundaryWeight.lean`.

This theorem is the main per-profile deliverable.

---

# Part III — optional actual fiber contribution theorem

If inexpensive, also prove the stronger semantic consumer:

```text
fiber.card
  * exp ((3/8) * profile mass)
<=
M(e)^(3/8).
```

Target shape:

```lean
theorem GNExcess_cubic_realizedLarge_fiberMoment_le_modulus_three_eighths ...
```

Use:

```lean
card_GNExactExcessProfileEvent_le_largeBoundary
```

for the canonical cubic prime family and then Part II.

This theorem makes the actual contribution explicit:

```text
actual fiber multiplicity
  ×
profile exponential weight
```

rather than only the root-address majorant.

It is strongly preferred if the proof is short.

Do not rebuild the CRT cardinal theorem.

---

# Part IV — define the realized cubic modulus moment

Define the new reduced large object.

Recommended shape:

```lean
noncomputable def GNExcessCubicRealizedLargeModulusMoment
    (X : ℕ) : ℝ :=
  ∑ excess ∈ GNExcessRealizedLargeProfileSpace
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X,
    (GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess : ℝ) ^
        (3/8 : ℝ)
```

If parameterizing `t` would obscure the fact that this object is specifically
the cubic `3/8` reduction, keep it fixed at `3/8`.

The name should make clear:

- cubic,
- realized,
- large,
- modulus moment.

Do not call this a density or ABC bound.

---

# Part V — aggregate realized boundary reduction

Prove:

```text
GNExcessRealizedLargeBoundaryProfileSum
  (GNNonExceptionalIntervalPrimeFamily 3 1 X)
  3 1 X (3/8)

<=

GNExcessCubicRealizedLargeModulusMoment X.
```

Recommended theorem name:

```lean
GNExcessRealizedLargeBoundaryProfileSum_cubic_three_eighths_le_modulusMoment
```

The proof should be a direct `Finset.sum_le_sum` application of Part II.

This is the main aggregate deliverable.

No profile counting estimate should be introduced here.

---

# Part VI — ghost-free cubic moment reduced to modulus moment

Compose LUNA-004 with Part V.

Target theorem:

```text
sum a in Icc 0 X,
  exp ((3/8) * GNExcessMassAt Q 3 1 a)

<=

2 * (X + 1) *
  GNExcessFiniteEulerDensity Q 3 1 X (3/8)

+

GNExcessCubicRealizedLargeModulusMoment X
```

where:

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X.
```

Recommended theorem name:

```lean
exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment
```

This theorem should be a short composition of:

```lean
exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic
```

and Part V.

This is the strongest production moment bridge targeted by LUNA-005.

---

# Part VII — height diagnostic corollary

Only after Parts I–VI compile cleanly, expose the immediate pointwise
height consequence.

For every realized canonical cubic large profile:

```text
(M(e) : ℝ)^(3/8)
<=
(3 * (X + 1)^2 : ℝ)^(3/8).
```

Use:

```lean
mem_realizedLargeProfileSpace_cubic_heightAdmissible
```

and monotonicity of `Real.rpow` on nonnegative reals.

If a cleaner normalized form is easy:

```text
<= 3^(3/8) * (X + 1)^(3/4)
```

it may be added.

However:

> This is a diagnostic per-profile bound, not the sought aggregate estimate.

Do not derive a crude `card * X^(3/4)` theorem unless it is needed for a
regression check. Such a theorem is mathematically too weak to be a research
target.

---

# What LUNA-005 is NOT

Do not attempt:

- a uniform bound for
  `GNExcessCubicRealizedLargeModulusMoment`,
- a linear or sublinear estimate for the realized modulus moment,
- an asymptotic count of realized profiles,
- a new CRT density theorem,
- a paired-orientation theorem,
- an `abcEpsilon` / quality coupling,
- a descent,
- a new ABC contract,
- any use of `abc_main_axiom`.

The objective is to **reduce** the realized large-boundary problem to a cleaner
arithmetic object, not to solve that object.

---

## Public import

If a new module is added, import it from `DkMath.ABC` immediately after
`GNExcessRealizedMoment` unless dependency order clearly suggests a nearby
placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

```bash
lake build DkMath.ABC.GNExcessCubicRealizedBoundary
lake build DkMath.ABC
```

Adjust the focused module name if needed.

Also:

- scan changed Lean files for `sorry`, `admit`, new `axiom`,
- confirm no reference to `abc_main_axiom`,
- audit axioms for:
  - the positive realized-large witness theorem,
  - the profile-level cubic `3/8` theorem,
  - the aggregate modulus-moment theorem,
  - the final cubic moment bridge.

Expected trust boundary:

```text
propext
Classical.choice
Quot.sound
```

or a subset thereof.

Existing unrelated repository warnings may remain and should be mentioned only
as unrelated warnings.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-005.md
```

Title:

```text
# LUNA-005 — cubic 3/8 realized-fiber transfer
```

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. declarations added,
3. how positivity of the realized large witness was obtained,
4. profile-level `3/8` boundary theorem,
5. whether the actual fiber contribution theorem was added,
6. definition of the realized large modulus moment,
7. aggregate boundary-to-modulus-moment theorem,
8. final cubic moment bridge,
9. whether the height diagnostic corollary was added,
10. focused build result,
11. ABC aggregator build result,
12. no-placeholder / no-new-axiom result,
13. axiom audit of principal theorems,
14. exact remaining mathematical blocker.

Update README / ROADMAP minimally if the checkpoint succeeds.

---

## Stop condition

Stop once the cubic `3/8` realized large-boundary contribution has been
reduced to:

```text
sum over actually realized large profiles e
  of M(e)^(3/8).
```

Do not autonomously attempt to bound that sum.

The next genuine research question is:

```text
What global arithmetic restrictions relate the distinct realized moduli M(e)
across the interval, strongly enough to control

  sum M(e)^(3/8) ?
```

LUNA-005 succeeds when the remaining large-boundary problem is expressed in
production Lean as a pure aggregate problem over **actual realized joint
moduli**, with ghost profiles and target-level root-address bookkeeping removed
from the frontier.
