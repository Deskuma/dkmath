# instruction-006 — realized cubic modulus-space extraction

## Mission

Continue the ABC–GN implementation phase after LUNA-005.

This checkpoint is **LUNA-006**.

LUNA-005 reduced the cubic realized large-boundary problem to

```text
sum over realized large profiles e of M(e)^(3/8),
```

where

```text
M(e) = GNExcessJointDepthModulus Q e
```

and

```text
Q = GNNonExceptionalIntervalPrimeFamily 3 1 X.
```

The next task is to remove the remaining profile-coordinate presentation as
far as possible and expose the **actual finite set of realized joint moduli**.

The desired structural chain is:

```text
realized large profile e
        |
        v
joint modulus M(e)
        |
        | injective on the canonical prime family
        v
distinct realized modulus M
        |
        v
exists actual a in [1, X]
        |
        v
M = GNNonExceptionalRepeatedPart 3 a 1
        |
        v
M divides GN 3 a 1 = a^2 + 3a + 3.
```

This is still an engineering/formalization checkpoint.

Do **not** attempt a global estimate for the modulus moment in this task.

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
report-005.md
instruction-005.md
```

Then inspect current production source, especially:

```text
DkMath/ABC/GNExcessActiveProfiles.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNExcessRealizableProfiles.lean
DkMath/ABC/GNExcessRealizedMoment.lean
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
DkMath/NumberTheory/GNThreeQuadratic.lean
```

Treat current source as authoritative.

---

## Reporting policy

Do **not** record branch HEAD hashes or commit hashes in `report-006.md`.

Git already records repository history.

Also fix the harmless section-title typo in
`GNExcessCubicRealizedBoundary.lean` if it is still present:

```text
Final LUNA-004 composition
```

should read:

```text
Final LUNA-005 composition
```

Do not otherwise refactor LUNA-005.

---

# Starting facts already in production

## Expanded joint modulus

```lean
GNExcessJointDepthModulus_eq_prod
```

gives:

```text
M(e)
=
∏ q ∈ GNExcessActivePrimeSet Q e,
  q^(GNExcessProfileValue Q e q + 1).
```

For the canonical interval family every `q ∈ Q` is prime.

## Realized large positive witness

```lean
GNExcessRealizedLargeProfileSpace_exists_positive_point
```

gives a positive exact-fiber witness for every canonical realized large
profile.

## Target modulus identity

```lean
GNExcessJointDepthModulus_target_eq_repeatedPart
```

identifies the target profile modulus with

```lean
GNNonExceptionalRepeatedPart.
```

## Repeated-part divisor theorem

```lean
GNNonExceptionalRepeatedPart_dvd_GN
```

shows the repeated part divides the original GN value.

## Cubic explicit formula

Reuse the existing cubic explicit theorem, currently named:

```lean
DkMath.NumberTheory.GN_three_dual_explicit
```

Do not introduce a new polynomial definition if a short specialization to
`b = 1` is enough.

## Cubic realized modulus moment

```lean
GNExcessCubicRealizedLargeModulusMoment
```

is currently indexed by realized large **profiles**.

LUNA-006 should show that this can equally be regarded as a sum over distinct
realized integer moduli.

---

# Part I — recover a profile coordinate from its joint modulus

First prove the local arithmetic fact needed for injectivity.

For a finite prime family `Q`, under

```text
∀ q ∈ Q, Nat.Prime q,
```

prove that the factorization exponent of the joint modulus at a family prime
recovers the encoded active depth.

A useful target shape is:

```text
q ∈ Q
  ->
(M(e)).factorization q
=
if 0 < GNExcessProfileValue Q e q then
  GNExcessProfileValue Q e q + 1
else
  0.
```

Recommended theorem name:

```lean
GNExcessJointDepthModulus_factorization_at
```

or a nearby repository-consistent name.

The exact right-hand side may use `excess q hq` rather than
`GNExcessProfileValue` if that makes the theorem cleaner.

Use the existing product formula and unique prime factorization / factorization
API.

Do not build a custom prime-factorization framework.

A helper theorem for positivity/nonzeroness of the modulus may reuse:

```lean
GNExcessJointDepthModulus_pos
```

---

# Part II — injectivity of the profile-to-modulus map

Using Part I, prove:

```text
(∀ q ∈ Q, Nat.Prime q)
  ->
Function.Injective (GNExcessJointDepthModulus Q).
```

Recommended theorem name:

```lean
GNExcessJointDepthModulus_injective
```

The intended proof is coordinatewise:

1. assume `M(e₁) = M(e₂)`,
2. compare factorization exponent at each `q ∈ Q`,
3. recover whether each excess coordinate is zero or positive,
4. recover the exact positive coordinate from exponent `e_q + 1`,
5. conclude by function extensionality.

Important:

- zero coordinates must be handled explicitly,
- do not silently assume every family prime is active,
- the theorem should require primality of the family unless current APIs prove
  a more general safe hypothesis.

If generic injectivity causes substantial API friction, it is acceptable to
prove only the canonical cubic-family specialization, but record this choice in
the report.

Do **not** assume injectivity without proving it.

---

# Part III — define the realized cubic large modulus space

Add a new production module.

Recommended file:

```text
DkMath/ABC/GNExcessCubicRealizedModuli.lean
```

A nearby name is acceptable if it better matches repository style.

Define:

```lean
noncomputable def GNExcessCubicRealizedLargeModulusSpace
    (X : ℕ) : Finset ℕ :=
  (GNExcessRealizedLargeProfileSpace
    (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X).image
      (GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X))
```

Use a local abbreviation for the canonical family if that makes proofs
readable.

Provide minimal membership API:

```text
M ∈ modulus space
  <->
exists realized large profile e, M(e) = M.
```

Recommended theorem:

```lean
mem_GNExcessCubicRealizedLargeModulusSpace_iff
```

---

# Part IV — cardinal preservation

Use the injectivity theorem to prove that passing from realized profiles to
realized moduli loses no multiplicity:

```text
card realizedLargeProfileSpace
=
card GNExcessCubicRealizedLargeModulusSpace.
```

Recommended theorem:

```lean
card_GNExcessCubicRealizedLargeModulusSpace
```

or an equality-oriented variant.

This is a structural theorem only.

Do not combine it with the crude per-profile height bound to claim a useful
aggregate estimate.

---

# Part V — rewrite the modulus moment over integer moduli

Prove the exact identity:

```text
GNExcessCubicRealizedLargeModulusMoment X
=
∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X,
  (M : ℝ)^(3/8).
```

Recommended theorem name:

```lean
GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace
```

This should use `Finset.sum_image` / an injective image-sum theorem.

The goal is to make the frontier no longer depend on the profile variable
`e`.

After this theorem, the large term should be readable as a sum over distinct
natural numbers.

---

# Part VI — realized modulus witness and quadratic divisor bridge

For every modulus in the canonical realized large modulus space, prove the
existence of a positive interval point realizing it.

Target theorem shape:

```lean
theorem GNExcessCubicRealizedLargeModulusSpace_exists_witness
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a : ℕ,
      0 < a ∧
      a ∈ Finset.Icc 0 X ∧
      M = GNNonExceptionalRepeatedPart 3 a 1
```

The equality orientation may be reversed if convenient.

Then prove the arithmetic divisor consumer:

```text
M ∈ realized modulus space
  ->
exists a,
  0 < a
  and a ≤ X
  and M ∣ GN 3 a 1.
```

Finally specialize the cubic formula:

```text
M ∣ a^2 + 3*a + 3.
```

Recommended theorem name:

```lean
GNExcessCubicRealizedLargeModulusSpace_dvd_quadratic
```

or a nearby name.

Use the existing:

```lean
GNNonExceptionalRepeatedPart_dvd_GN
GN_three_dual_explicit
```

Do not reprove divisibility through factorization.

---

# Part VII — structural properties of each realized modulus

For every

```text
M ∈ GNExcessCubicRealizedLargeModulusSpace X,
```

prove the cheap properties already implied by existing production theorems.

## Large lower bound

```text
X + 1 < M.
```

## Cubic height upper bound

```text
M ≤ 3 * (X + 1)^2.
```

Reuse the realized cubic height theorem.

## Positivity

```text
0 < M.
```

This should be immediate from the prime-family modulus positivity or from
`X + 1 < M`.

## Squareful support

Prefer a useful theorem such as:

```text
Nat.Prime q
  ->
q ∣ M
  ->
q^2 ∣ M.
```

Reuse the repeated-part packet / repeated-part theorem through a realized
witness.

## Cubic prime-shell condition

If inexpensive, also prove:

```text
Nat.Prime q
  ->
q ∣ M
  ->
q % 3 = 1.
```

Reuse existing non-exceptional support/order-prime theorems.

Do not reprove the cubic shell arithmetic.

These structural theorems make the extracted modulus space a self-contained
integer object suitable for the next research pass.

---

# Part VIII — optional compact certificate structure

Only if Parts I–VII are already clean, a small structure may be introduced to
package the integer facts for one modulus, for example:

```lean
structure GNExcessCubicRealizedModulusPacket (X M : ℕ) where
  interval_lt : X + 1 < M
  height_le : M ≤ 3 * (X + 1)^2
  witness : ℕ
  witness_pos : 0 < witness
  witness_le : witness ≤ X
  dvd_quadratic : M ∣ witness^2 + 3*witness + 3
  prime_sq_dvd : ...
  prime_mod_three_eq_one : ...
```

Then construct it from membership in the modulus space.

This is optional.

Do not introduce the structure if it merely duplicates theorems and makes the
API heavier.

---

# Part IX — final frontier theorem/corollary

Update the LUNA-005 final moment theorem with the Part V rewrite, either by a
new corollary or a short theorem in the new module.

Desired readable endpoint:

```text
actual cubic 3/8 moment
<=
2*(X+1)*finiteEuler
+
∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X,
    M^(3/8).
```

Recommended theorem name:

```lean
exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_realizedModuli
```

This theorem should be a short composition/rewrite.

It is the preferred human-readable endpoint after LUNA-006.

---

# What LUNA-006 is NOT

Do not attempt:

- a bound for the cardinality of the modulus space sharper than what follows
  trivially from the profile image,
- a bound for
  `∑ M ∈ modulusSpace, M^(3/8)`,
- an asymptotic theorem for squareful divisors of the quadratic,
- a new sieve or CRT-density theorem,
- paired-orientation coupling,
- `abcEpsilon` / quality coupling,
- descent,
- any new ABC-equivalent contract,
- any use of `abc_main_axiom`.

The goal is **extraction and exact reindexing**, not the aggregate estimate.

---

## Important falsification boundary

Do not assume that distinct interval points produce distinct moduli.

The injectivity target is:

```text
profile -> modulus
```

not:

```text
point -> modulus.
```

A single exact profile may have multiple interval points in its fiber.

Likewise, do not claim that every squareful divisor of
`a^2 + 3a + 3` belongs to the realized modulus space.

Only the forward implication from realized modulus membership is requested.

---

## Public import

If a new module is added, import it from `DkMath.ABC` immediately after
`GNExcessCubicRealizedBoundary` unless current dependency order clearly
requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

```bash
lake build DkMath.ABC.GNExcessCubicRealizedModuli
lake build DkMath.ABC
```

Adjust the focused module name if needed.

Also:

- scan changed Lean files for `sorry`, `admit`, new `axiom`,
- confirm no reference to `abc_main_axiom`,
- audit axioms for:
  - profile-to-modulus injectivity,
  - modulus-space moment reindex,
  - quadratic divisor theorem,
  - final realized-moduli moment bridge.

Expected trust boundary:

```text
propext
Classical.choice
Quot.sound
```

or a subset thereof.

Existing unrelated repository warnings should be mentioned only as unrelated
warnings.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-006.md
```

Title:

```text
# LUNA-006 — realized cubic modulus-space extraction
```

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. declarations added,
3. factorization-coordinate recovery theorem,
4. whether injectivity was generic or canonical-cubic only,
5. modulus-space definition,
6. cardinal preservation,
7. exact modulus-moment rewrite,
8. positive interval witness theorem,
9. quadratic divisor theorem,
10. lower/upper modulus bounds,
11. squareful and mod-3 support properties completed,
12. whether an optional packet structure was added,
13. final human-readable moment bridge,
14. focused build result,
15. ABC aggregator build result,
16. no-placeholder / no-new-axiom result,
17. axiom audit,
18. exact remaining mathematical blocker,
19. any factorization / Finset API friction.

Update README / ROADMAP minimally if the checkpoint succeeds.

---

## Stop condition

Stop once the LUNA-005 modulus moment is exactly expressed over a finite set of
distinct natural-number moduli and every member has a production certificate
of the form:

```text
X + 1 < M ≤ 3*(X+1)^2

exists 1 ≤ a ≤ X,
  M = GNNonExceptionalRepeatedPart 3 a 1
  and
  M ∣ a^2 + 3a + 3

every prime q | M:
  q^2 | M
  and
  q ≡ 1 (mod 3).
```

Do not autonomously attempt to estimate the resulting modulus sum.

The next genuine research question is then entirely arithmetic:

```text
How large can

  ∑ M^(3/8)

be over the distinct realized squareful divisors M of cubic GN values
a^2 + 3a + 3, subject to the interval and prime-shell constraints?
```

At that point, the profile machinery has done its job and the next branch
decision should be based on the integer modulus geometry itself.
