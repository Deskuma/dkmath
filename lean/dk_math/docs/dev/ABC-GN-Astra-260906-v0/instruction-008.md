# instruction-008 — LUNA canonical repeated/complement foundation

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-008**.

ASTRA-007 ended at a genuine research boundary.  Do not continue that research
here.  Instead promote only the stable, kernel-checked structural facts from
`scratch-007.lean.txt` into production Lean.

The central new arithmetic coordinate is

```text
F(a) = a^2 + 3*a + 3
     = M(a) * S(a)

M(a) = full repeated prime-power part
S(a) = residual complement.
```

For the canonical cubic family, ASTRA-007 already checked in Lean scratch that

```text
M(a) = GNNonExceptionalRepeatedPart 3 a 1

S(a) is squarefree

Coprime M(a) S(a)

and for a realized large modulus with witness a <= X:

S(a) <= X.
```

LUNA-008 should make these facts durable production API, together with the
exact quadratic root-spacing lemma.

No incidence estimate, no paired relative-height theorem, and no ABC closure
should be attempted.

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
report-007.md
review-007.md
scratch-007.lean.txt
validation-007.txt
report-006.md
```

Then inspect current production source, especially:

```text
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNExcessCubicRealizedModuli.lean
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
DkMath/NumberTheory/GNThreeQuadratic.lean
```

Treat current production source as authoritative.

---

## Reporting policy

Do **not** record branch HEAD hashes or commit hashes in `report-008.md`.

Git already records repository history.

The report should describe mathematical declarations, proof dependencies,
verification, and the remaining research boundary.

---

# Part I — canonical cubic prime-3 repeated-depth exclusion

Promote the ASTRA scratch fact:

```lean
not_nine (a : ℕ) :
  ¬ 9 ∣ a^2 + 3*a + 3
```

Use a production-quality name, for example:

```lean
not_nine_dvd_GN_three_one
```

or:

```lean
nine_not_dvd_cubic_quadratic
```

A theorem stated directly on `GN 3 a 1` may also be useful:

```lean
¬ 3^2 ∣ GN 3 a 1
```

If both forms are cheap, expose one as the core theorem and the other as a
short corollary.

Reuse the existing explicit cubic formula.

Do not build a general p-adic theorem here.

---

# Part II — full repeated part equals the canonical non-exceptional repeated part

Promote the scratch theorem:

```text
GNNonExceptionalRepeatedPart 3 a 1
=
repeatedPrimePowerPart (GN 3 a 1).
```

Recommended theorem name:

```lean
GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart
```

or a nearby repository-consistent name.

The proof should use Part I to show that excluding prime 3 removes no
prime-power factor of depth at least two.

Do not duplicate a large factorization proof if a cleaner production proof can
reuse existing support/factorization API.

This theorem is a key semantic simplification and should have a clear docstring.

---

# Part III — generic repeated-prime-power complement API

The ASTRA scratch proved a useful theorem for arbitrary nonzero natural
numbers.

Prefer introducing a small reusable definition:

```lean
def repeatedPrimePowerComplement (n : ℕ) : ℕ :=
  n / repeatedPrimePowerPart n
```

A different concise name is acceptable if it matches existing DkMath style.

Then prove the generic facts for `n ≠ 0`:

```text
repeatedPrimePowerPart n * repeatedPrimePowerComplement n = n

Squarefree (repeatedPrimePowerComplement n)

Nat.Coprime
  (repeatedPrimePowerPart n)
  (repeatedPrimePowerComplement n).
```

Recommended theorem family:

```lean
repeatedPrimePowerPart_mul_complement
squarefree_repeatedPrimePowerComplement
coprime_repeatedPrimePowerPart_complement
```

or an equivalent bundled theorem plus projections.

Use the exact scratch proof as a starting point:

```lean
complement_decomposition
```

but give the production API names independent of ASTRA.

Important semantic point:

> this complement removes **all** prime powers whose exponent is at least two,
> including odd exponents in full.

It is **not** the parity squarefree kernel.

Mention this in the docstring to prevent future misuse.

---

# Part IV — canonical cubic complement definition

Define the canonical cubic residual complement.

Recommended shape:

```lean
def GNExcessCubicComplement (a : ℕ) : ℕ :=
  GN 3 a 1 / GNNonExceptionalRepeatedPart 3 a 1
```

A nearby name such as `GNCubicRepeatedComplement` is acceptable.

Then prove:

```text
GNNonExceptionalRepeatedPart 3 a 1
  * GNExcessCubicComplement a
=
GN 3 a 1
```

and the explicit quadratic form:

```text
GNNonExceptionalRepeatedPart 3 a 1
  * GNExcessCubicComplement a
=
a^2 + 3*a + 3.
```

Also prove:

```text
Squarefree (GNExcessCubicComplement a)

Nat.Coprime
  (GNNonExceptionalRepeatedPart 3 a 1)
  (GNExcessCubicComplement a).
```

These should be direct consumers of Parts II–III.

Do not reprove the generic factorization argument in the canonical layer.

---

# Part V — realized large modulus obtains a canonical complement certificate

This is the main consumer API of LUNA-008.

For:

```text
M ∈ GNExcessCubicRealizedLargeModulusSpace X
```

reuse the existing positive witness theorem and prove existence of `a` and
the canonical complement `S` with the complete certificate.

Preferred theorem shape:

```lean
theorem GNExcessCubicRealizedLargeModulusSpace_exists_complement_packet
    {X M : ℕ}
    (hX : 0 < X)
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a S : ℕ,
      0 < a ∧
      a ≤ X ∧
      M = GNNonExceptionalRepeatedPart 3 a 1 ∧
      S = GNExcessCubicComplement a ∧
      M * S = a^2 + 3*a + 3 ∧
      Squarefree S ∧
      Nat.Coprime M S ∧
      S ≤ X
```

Exact conjunction order and theorem name may be adjusted.

If a small structure makes this substantially cleaner, a structure is allowed,
for example:

```lean
structure GNExcessCubicComplementPacket (X M : ℕ) where
  witness : ℕ
  complement : ℕ
  witness_pos : 0 < witness
  witness_le : witness ≤ X
  modulus_eq_repeated : ...
  quadratic_decomp : ...
  complement_squarefree : ...
  coprime : ...
  complement_le : complement ≤ X
```

However, do not introduce a structure merely for aesthetics.

The key new production theorem is the **sharp complement bound**:

```text
S ≤ X
```

under the realized-large condition.

Reuse the ASTRA scratch theorem `complement_sharp`; do not weaken it back to
`S ≤ X+1`.

Handle the edge case `X = 0` explicitly.  If the realized-large modulus space
is empty at `X=0`, either prove that and remove the `0 < X` hypothesis, or
keep `hX : 0 < X` if it gives a cleaner API.

Do not hide a nontrivial zero-case assumption.

---

# Part VI — quadratic root-difference and spacing lemmas

Promote the two ASTRA scratch facts.

For

```text
F(a) = a^2 + 3*a + 3,
```

prove the integer divisibility identity:

```text
M ∣ F(a)
M ∣ F(b)

=>

(M : ℤ) ∣ (b-a)*(a+b+3).
```

Recommended theorem name:

```lean
cubicQuadratic_commonDivisor_dvd_rootDifference
```

or similar.

Then prove the natural-number spacing theorem for `a < b`:

```text
M ∣ F(a)
M ∣ F(b)
a < b

=>

M ≤ (b-a)*(a+b+3).
```

Recommended theorem name:

```lean
cubicQuadratic_commonDivisor_le_spacingProduct
```

or similar.

These are elementary arithmetic facts and should not depend on realizability.

Do not attempt a global cardinality theorem from spacing in this checkpoint.

An optional short interval corollary is allowed if completely routine:

```text
a,b ≤ X
=>
M ≤ (b-a)*(2*X+3).
```

But it is not required.

---

# Part VII — negative regression protection

ASTRA-007 falsified point-to-modulus injectivity and the at-most-two shortcut.

Preserve at least the following exact regressions in a **test/research module**,
not as prominent production API:

```text
GNNonExceptionalRepeatedPart 3 21 1 = 169
GNNonExceptionalRepeatedPart 3 145 1 = 169
```

and the four-root example:

```text
GNNonExceptionalRepeatedPart 3 2173 1 = 8281
GNNonExceptionalRepeatedPart 3 3018 1 = 8281
GNNonExceptionalRepeatedPart 3 5260 1 = 8281
GNNonExceptionalRepeatedPart 3 6105 1 = 8281.
```

Recommended location:

```text
DkMathTest/ABC/GNCubicComplementRegression.lean
```

or the existing Astra test module if that is more natural.

These examples exist to prevent future false claims such as:

```text
point -> repeated modulus is injective

one full repeated modulus has at most two roots.
```

Do not add giant regression proofs to the public ABC facade unless repository
style already does so.

Use the persisted ASTRA factorization certificates as source material.

---

# Part VIII — do not productionize research conjectures

The following ASTRA-007 findings are **not** production theorems and must remain
out of this checkpoint:

```text
N_X(D) ≤ C_epsilon * X^(1+epsilon) / sqrt(D)

any linear bound for the modulus moment

paired relative-large exclusion

both orientations cannot simultaneously exceed a+1

a uniform bound on complement multiplicity

a uniform small bound on modulus witness multiplicity.
```

Likewise, do not turn these into structures, provider classes, assumptions, or
renamed contracts.

The numerical paired signal remains research-only.

---

# Part IX — defer Pell and squarefull obstruction to later fact-freezing checkpoints

ASTRA-007 also contains compiled:

```text
pell_invariant
pell_repeated
pell_strictMono
pell_complement

squarefull_block_obstruction
```

These are useful and should eventually be frozen, but LUNA-008 should stay
focused on the core complement/spacing foundation.

Do not add them unless Parts I–VII are already trivial and the resulting module
layout remains clean.

Preferred workflow:

```text
LUNA-008:
  canonical complement + spacing + collision regressions

later Luna checkpoint:
  Pell obstruction / incidence-obstruction ledger
```

---

## Suggested production module layout

Preferred new module:

```text
DkMath/ABC/GNExcessCubicComplement.lean
```

It may contain:

- prime-3 repeated-depth exclusion,
- full repeated-part equality,
- generic complement API,
- canonical complement API,
- realized complement certificate,
- quadratic spacing.

If the generic complement API clearly belongs one layer lower, it is acceptable
to place that small generic section in `GNExcessLargeBoundaryPacket.lean` and
keep the cubic consumers in the new module.

Avoid broad refactoring.

Publicly import the new cubic complement module from `DkMath.ABC` immediately
after `GNExcessCubicRealizedModuli` unless dependency order suggests a nearby
placement.

---

## Verification

At minimum run:

```bash
lake build DkMath.ABC.GNExcessCubicComplement
lake build DkMath.ABC
```

Also build the regression test module if added.

Scan all changed production Lean files for:

```text
sorry
admit
new axiom
abc_main_axiom
native_decide
```

None may be introduced.

The ASTRA scratch used ordinary kernel-checkable factorization certificates;
keep that trust boundary.

Audit axioms for the principal new theorems:

- canonical full repeated-part equality,
- generic squarefree complement theorem,
- generic coprimality theorem,
- realized-large complement certificate / `S ≤ X`,
- spacing theorem.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-008.md
```

Title:

```text
# LUNA-008 — canonical repeated/complement foundation
```

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. declarations added,
3. prime-3 repeated-depth exclusion,
4. full repeated-part equality,
5. generic complement API,
6. canonical cubic complement API,
7. realized-large complement certificate,
8. exact proof of `S ≤ X`,
9. spacing theorems,
10. negative regression examples preserved,
11. focused build result,
12. ABC aggregator build result,
13. regression-test build result if applicable,
14. no-placeholder / no-new-axiom result,
15. axiom audit,
16. exact remaining research frontier.

Update README / ROADMAP minimally if the checkpoint succeeds.

---

## Stop condition

Stop when the ASTRA-007 stable arithmetic has been promoted to production in
the following form:

```text
For every realized canonical cubic large modulus M:

exists 1 <= a <= X and S <= X,

  a^2 + 3*a + 3 = M*S,

  M = full repeated prime-power part of F(a),

  S is squarefree,

  gcd(M,S) = 1.
```

and the common-divisor spacing theorem is production-proved.

Do not continue into a quantitative incidence estimate.

The research frontier after LUNA-008 remains:

```text
control the global incidence distribution of

  F(a) = M*S

with
  M > X,
  S <= X,
  S squarefree,
  gcd(M,S)=1,

strongly enough to bound the distinct realized modulus 3/8 moment.
```

For now, the purpose is only to make the arithmetic coordinate system
trustworthy and reusable.
