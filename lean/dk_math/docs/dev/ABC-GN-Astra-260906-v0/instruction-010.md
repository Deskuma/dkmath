# instruction-010 — LUNA realized-modulus dyadic bookkeeping

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-010**.

LUNA-009 froze the Pell obstruction and the exact squarefull-block
necessary-condition theorem.  The open research frontier is still the global
incidence distribution of the distinct realized cubic moduli.

Do **not** attempt that incidence theorem here.

Instead, freeze the deterministic dyadic bookkeeping that will eventually
connect any future shell-count theorem to the existing realized modulus
`3/8` moment.

The desired production pipeline is:

~~~text
realized modulus space
        |
        v
exact dyadic shell partition
        |
        v
shell count × shell top weight
        |
        v
shell moment
        |
        v
sum of shell moments
=
GNExcessCubicRealizedLargeModulusMoment.
~~~

No new number-theoretic sparsity claim is part of this checkpoint.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read first:

~~~text
report-009.md
report-008.md
report-007.md
review-007.md
~~~

Then inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicRealizedModuli.lean
DkMath/ABC/GNExcessCubicRealizedBoundary.lean
DkMath/ABC/GNExcessCubicIncidenceObstruction.lean
~~~

Treat current production source as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in `report-010.md`.

The report should describe the finite-set identities, exact inequalities,
verification, and remaining research boundary.

---

# Part I — realized dyadic shell

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicRealizedDyadic.lean
~~~

Define the shell of realized moduli in the half-open interval `[D,2D)`.

Recommended shape:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShell
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusSpace X).filter
    (fun M => D ≤ M ∧ M < 2 * D)
~~~

Exact name is flexible but should clearly contain:

- cubic,
- realized,
- large modulus,
- shell.

Provide the basic membership theorem:

~~~text
M ∈ shell X D
<->
M ∈ realizedModulusSpace X
and D ≤ M
and M < 2D.
~~~

Also prove the shell is a subset of the realized modulus space.

Do not build an abstract dyadic framework for arbitrary finite sets unless it
makes the implementation shorter.

---

# Part II — shell count and shell moment

Define:

~~~lean
def GNExcessCubicRealizedLargeModulusShellCount
    (X D : ℕ) : ℕ :=
  (GNExcessCubicRealizedLargeModulusShell X D).card
~~~

and:

~~~lean
noncomputable def GNExcessCubicRealizedLargeModulusShellMoment
    (X D : ℕ) : ℝ :=
  ∑ M ∈ GNExcessCubicRealizedLargeModulusShell X D,
    (M : ℝ) ^ (3 / 8 : ℝ)
~~~

These are exact finite objects.

Do not call the shell count an incidence bound.

It is only the quantity that a future incidence theorem must estimate.

---

# Part III — elementary upper and lower shell weight bounds

For one shell, prove the exact deterministic inequalities.

## Lower shell weight

A preferred theorem shape is:

~~~text
(shell.card : ℝ) * (D : ℝ)^(3/8)
<=
shellMoment X D.
~~~

Every member satisfies `D ≤ M`.

Recommended name:

~~~lean
GNExcessCubicRealizedLargeModulusShell_card_mul_lowerWeight_le_moment
~~~

## Upper shell weight

Prove:

~~~text
shellMoment X D
<=
(shell.card : ℝ) * ((2*D : ℕ) : ℝ)^(3/8).
~~~

Using `M < 2D` and monotonicity of `Real.rpow`.

Recommended name:

~~~lean
GNExcessCubicRealizedLargeModulusShell_moment_le_card_mul_upperWeight
~~~

A slightly sharper upper endpoint using `2*D-1` is unnecessary.

Keep the simple `2D` form.

These are bookkeeping theorems, not estimates for the cardinality.

---

# Part IV — shell-count hypothesis consumer

Expose a generic one-shell implication.

For example, if:

~~~text
(shell.card : ℝ) ≤ B
~~~

then:

~~~text
shellMoment X D
<=
B * (2D)^(3/8).
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShell_moment_le_of_card_le
~~~

Do not introduce a typeclass, provider, or global assumption.

The count bound must be an explicit theorem argument.

This theorem exists only so a future incidence theorem can plug into the
moment machinery with no new algebraic work.

---

# Part V — dyadic index attached to an actual modulus

Use the standard natural logarithm base two.

For a positive natural `M`, the canonical dyadic index is:

~~~text
k = Nat.log 2 M.
~~~

Prove or reuse the standard facts:

~~~text
2^k ≤ M
M < 2^(k+1).
~~~

Do not reprove logarithm theory if Mathlib already provides these.

If the available theorem names make direct use awkward, isolate a tiny helper
lemma local to the new module.

The realized modulus is always positive, so no zero ambiguity occurs.

---

# Part VI — finite realized dyadic index space

Define the set of dyadic indices actually used by realized moduli:

~~~lean
noncomputable def GNExcessCubicRealizedLargeDyadicIndexSpace
    (X : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusSpace X).image
    (Nat.log 2)
~~~

If `Nat.log 2` elaboration requires an explicit lambda, use one.

Provide membership API:

~~~text
k ∈ indexSpace X
<->
exists M ∈ realizedModulusSpace X,
  Nat.log 2 M = k.
~~~

No asymptotic bound on the number of indices is required.

---

# Part VII — exact dyadic shell partition

For the canonical shell base

~~~text
D_k = 2^k,
~~~

prove that the realized modulus space is exactly covered by the shells indexed
by the realized dyadic index space.

A preferred finite-set theorem is conceptually:

~~~text
biUnion k in indexSpace X,
  GNExcessCubicRealizedLargeModulusShell X (2^k)
=
GNExcessCubicRealizedLargeModulusSpace X.
~~~

The equality orientation may be reversed.

Also prove the relevant pairwise disjointness, or use a unique-index argument
inside the sum theorem below.

Important:

- the shells are half-open `[2^k,2^(k+1))`,
- each positive modulus has exactly one such index,
- no modulus may be counted twice.

Do not accept an inequality when an exact partition is routine.

---

# Part VIII — exact modulus-moment reindex by dyadic shells

This is the main LUNA-010 deliverable.

Prove:

~~~text
GNExcessCubicRealizedLargeModulusMoment X
=
∑ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
  GNExcessCubicRealizedLargeModulusShellMoment X (2^k).
~~~

Recommended theorem name:

~~~lean
GNExcessCubicRealizedLargeModulusMoment_eq_sum_dyadicShellMoments
~~~

Use the existing exact identity:

~~~lean
GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace
~~~

and the shell partition.

This theorem must be an exact reindexing, not a majorant.

After this theorem the open frontier can be stated shell-by-shell without
changing the mathematical object.

---

# Part IX — generic shell-count-to-global-moment consumer

If clean, prove a provider-free finite theorem of the following form.

Given a function:

~~~lean
B : ℕ → ℝ
~~~

and hypotheses:

~~~text
for every k in realized dyadic index space,

  shellCount(X,2^k) ≤ B(k)
~~~

prove:

~~~text
GNExcessCubicRealizedLargeModulusMoment X
<=
∑ k in realized dyadic index space,
  B(k) * (2^(k+1) : ℝ)^(3/8).
~~~

Exact cast placement may vary.

Recommended theorem name:

~~~lean
GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds
~~~

This is a purely formal consumer of explicit hypotheses.

Do not name `B` an incidence provider.

Do not instantiate it with the unproved ASTRA target.

If this theorem becomes cumbersome, Parts I–VIII have priority.

---

# Part X — height-derived empty-shell guards

Expose the cheap empty-shell facts implied by existing production bounds.

## Above cubic height

If:

~~~text
3*(X+1)^2 < D
~~~

then the shell at D is empty.

A slightly weaker assumption such as `3*(X+1)^2 < D` is sufficient because
every realized modulus is at most the cubic height.

## Entirely below the large boundary

If:

~~~text
2*D ≤ X+2
~~~

then every `M < 2D` satisfies `M ≤ X+1`, so the realized-large shell is
empty.

Exact off-by-one hypotheses may be adjusted to whatever gives a clean natural
number proof.

These are useful finite-support guards, not counting estimates.

---

# Part XI — optional dyadic endpoint constraints

For:

~~~text
k ∈ realized dyadic index space X
~~~

it is useful, if cheap, to expose:

~~~text
X+1 < 2^(k+1)

2^k ≤ 3*(X+1)^2.
~~~

These follow from an actual modulus in that shell plus the production
lower/upper modulus bounds.

They make the eventual exponent arithmetic easier.

Do not derive logarithmic asymptotics.

---

# Part XII — keep the research target external

ASTRA-007 proposed a sufficient research target resembling:

~~~text
N_X(D)
<=
C_epsilon * X^(1+epsilon) / sqrt(D).
~~~

LUNA-010 must **not** prove, assume globally, package, or rename this statement.

It may be mentioned in docstrings only as motivation for why the shell-count
API exists.

Likewise, do not introduce:

- epsilon constants,
- asymptotic notation,
- Big-O,
- a density provider,
- an ABC receiver theorem.

The output of this checkpoint is exact finite combinatorics only.

---

## Public import

Import the new module from `DkMath.ABC` after:

~~~text
GNExcessCubicIncidenceObstruction
~~~

unless dependency order suggests placement immediately before it.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~bash
lake build DkMath.ABC.GNExcessCubicRealizedDyadic
lake build DkMath.ABC
~~~

Adjust the focused module name if needed.

Scan changed Lean files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit axioms for:

- shell lower/upper moment bounds,
- dyadic shell partition,
- exact modulus-moment dyadic reindex,
- global card-bound consumer if implemented.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

---

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-010.md
~~~

Title:

~~~text
# LUNA-010 — realized-modulus dyadic bookkeeping
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. shell definition,
3. shell count / moment definitions,
4. elementary lower/upper shell moment bounds,
5. one-shell count consumer,
6. realized dyadic index space,
7. exact shell partition,
8. exact modulus-moment reindex,
9. global explicit-card-bound consumer status,
10. empty-shell guards,
11. optional endpoint constraints,
12. focused build,
13. ABC aggregator build,
14. no-placeholder / no-new-axiom result,
15. axiom audit,
16. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the current realized modulus moment has an exact dyadic-shell
representation:

~~~text
modulusMoment(X)
=
sum over actual dyadic shells
  shellMoment(X,D),
~~~

and every shell has the deterministic bound:

~~~text
shellMoment(X,D)
<=
shellCount(X,D) * (2D)^(3/8).
~~~

Do not attempt to estimate `shellCount`.

After LUNA-010 the research frontier should be expressible with no remaining
bookkeeping ambiguity:

~~~text
prove a genuinely new arithmetic bound on the exact finite quantity

  GNExcessCubicRealizedLargeModulusShellCount X D

for D in the realized large range.
~~~

That theorem is research.

LUNA-010 only makes the target precise and mechanically connected to the
existing ABC–GN moment reduction.
