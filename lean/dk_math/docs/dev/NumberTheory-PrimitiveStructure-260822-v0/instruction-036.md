# Codex Instruction — PRIM-JAC-000 Jacobsthal / Primorial Coprime-Gap Frontier Audit

Branch: `wip/number-theory-primitive-structure-260822-v2`

Project: DkMath NumberTheory Primitive Structure / Legendre first application

Environment: keep the repository on Lean / Mathlib v4.32.2. Do not upgrade the toolchain.

## Checkpoint type

This is a **read-only mathematical/API reconnaissance**.

Do **not** modify Lean source files, theorem statements, docstrings, imports, facades, dependencies, `lean-toolchain`, Lake configuration, PRIM-C001/C002, PRIM-L022, or the existing Legendre frontier.

Produce one report only:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-jacobsthal-frontier-audit-260825.md
```

The purpose is to determine whether the current exact Legendre frontier is best understood as an anchored Jacobsthal / primorial coprime-gap problem, and whether that reformulation supplies any new leverage or only a sharper identification of the remaining hard provider.

---

# Current verified context

The current project already has:

```text
primeScalesUpTo n
primeWorldModulus (primeScalesUpTo n)
SupportDisjointFrom
SquareOffset
SquareOffsetsFullyCovered
SquareAnchoredSupportEscape
LegendreConjecture
```

and exact equivalences showing that Legendre is equivalent to failure of complete old-prime-wave cover in the square shell.

The Primitive periodic observer also has:

```lean
supportDisjointFrom_iff_coprime_primeWorldModulus
```

for a certified finite prime world.

Therefore, for

```text
M(n) := primeWorldModulus (primeScalesUpTo n),
```

support escape should be equivalent to coprimality with `M(n)`.

The square shell consists exactly of the `2*n` consecutive integers

```text
n^2 + 1, ..., n^2 + 2*n.
```

The audit must determine the exact relation between the current DkMath frontier and the classical Jacobsthal-type statement that every sufficiently long consecutive block contains an integer coprime to a given modulus.

---

# Critical distinction to preserve

Do not silently identify the Legendre frontier with the global Jacobsthal function.

The current DkMath target is **anchored** at `n^2`:

```text
there exists r with 1 ≤ r ≤ 2*n such that Coprime (n^2+r) M(n).
```

The classical Jacobsthal function `j(M)` is a **uniform all-starting-points** quantity:

```text
any block of j(M) consecutive integers contains an integer coprime to M.
```

Thus a bound such as

```text
j(M(n)) ≤ 2*n
```

would be sufficient for the DkMath target, but it is not automatically equivalent to the anchored square statement.

The report must classify each relation explicitly as one of:

```text
EXACT EQUIVALENCE
SUFFICIENT BUT STRONGER
NECESSARY BUT WEAKER
UNRELATED / WRONG TARGET
```

---

# Q1 — canonical modulus / primorial identification

Audit the exact meaning of

```lean
primeWorldModulus (primeScalesUpTo n)
```

and determine whether it is extensionally the product of all primes `p ≤ n`.

Clarify its relation to standard primorial notation:

- if `n` is prime, it is `n#`;
- for arbitrary `n`, it is the primorial of the largest prime at most `n`;
- no theorem should assume `n` itself prime.

Prefer existing DkMath/Mathlib product lemmas. Do not add a new primorial definition.

Report the smallest existing theorem chain needed to justify the identification.

---

# Q2 — support escape ↔ coprimality with the bounded-prime modulus

Using existing APIs, verify the exact chain

```text
SupportDisjointFrom (primeScalesUpTo n) m
↔ Coprime m M(n)
↔ no prime p ≤ n divides m.
```

Determine whether all three directions already exist as public theorems or whether one direction would require only a thin bridge.

Do not implement the bridge in this checkpoint.

---

# Q3 — exact anchored coprime-gap form of Legendre

Expand the current frontier to the raw statement

```text
∀ n > 0,
  ∃ r,
    1 ≤ r ∧ r ≤ 2*n ∧
    Nat.Coprime (n^2 + r) M(n).
```

Determine whether this is already derivable from the existing theorem chain by rewriting only, and classify it as:

```text
LegendreConjecture
↔ anchored bounded-prime coprime escape
```

if and only if the source supports the full equivalence.

This should not be confused with a new proof.

---

# Q4 — define the report-local anchored gap quantity

For analysis only, introduce report-local notation such as

```text
A(n) := least r ≥ 1 such that Coprime (n^2+r) M(n)
```

or, if a least-value formulation is awkward, use the equivalent existence statement over `1 ≤ r ≤ 2*n`.

Do not add a Lean definition.

Determine whether Legendre is exactly

```text
A(n) ≤ 2*n
```

for every positive `n`.

Record any zero/nonexistence edge cases carefully.

---

# Q5 — classical Jacobsthal function comparison

Audit the standard Jacobsthal function definition from reliable mathematical references:

```text
j(M) = least L such that every block of L consecutive integers contains a number coprime to M.
```

Clearly separate external mathematical literature from repository-derived facts.

Then compare:

```text
A(n) ≤ 2*n
```

with

```text
j(M(n)) ≤ 2*n.
```

Required conclusions:

1. Prove/report whether the Jacobsthal bound implies the anchored DkMath target.
2. Determine whether the converse is false in general as a logical matter because the anchored target controls only one starting point.
3. Do not claim strict separation for this specific modulus family unless a proof or counterexample is found.
4. If the precise inequality needs an off-by-one convention (`j`, block length, maximum run length), document it explicitly and normalize before comparison.

---

# Q6 — known Jacobsthal bounds versus the Legendre scale

Using reliable literature, audit whether known general upper bounds for the Jacobsthal function are strong enough to imply

```text
j(M(n)) ≤ 2*n
```

for all sufficiently large `n`, or for all `n` after finite verification.

Be precise about the parameter used in the literature:

```text
ω(M(n)) = number of primes ≤ n = π(n).
```

Do not turn asymptotic notation with an unspecified constant into an explicit theorem strong enough for Legendre.

Classify each candidate bound as:

```text
TOO WEAK AT THE REQUIRED SCALE
ASYMPTOTIC BUT CONSTANT UNCONTROLLED
EXPLICIT AND POTENTIALLY SUFFICIENT
SUFFICIENT AFTER FINITE CHECK
```

Only claim the last two if the inequalities actually work.

This section may conclude that the global Jacobsthal route is strictly stronger and currently not known at the needed scale.

---

# Q7 — relation to the existing DkMath wave / carry / overlap stack

Compare the Jacobsthal viewpoint with the already implemented exact local counting machinery:

```text
squareWaveOffsets
squareWaveCarry
pair overlap
near/far split
localized obstruction ledgers
packet cross geometry
```

Determine whether the Jacobsthal reformulation:

- adds a genuinely new theorem;
- merely packages the same union-of-residue-waves problem as a maximal coprime gap;
- exposes a known external theorem family that can consume the exact DkMath modulus;
- loses the square anchor geometry by passing to a uniform all-interval bound.

Do not add inclusion-exclusion, Hall matching, or analytic sieve machinery in this checkpoint.

---

# Q8 — periodicity and reduction modulo M(n)

Because DkMath already proves support periodicity modulo the finite-world modulus, inspect whether the anchored shell problem can be reduced exactly to the residue block

```text
n^2 + 1, ..., n^2 + 2*n mod M(n).
```

Clarify what this does and does not buy:

- it makes the problem finite for each fixed `n`;
- it does not give a uniform proof over all `n`;
- `M(n)` grows with `n`, so one cannot fix one finite automaton/modulus for the full conjecture.

Check whether centered mirror symmetry around multiples of `M(n)` has any concrete implication for the specific anchor `n^2`.

Do not infer that periodicity itself produces a survivor.

---

# Q9 — exact frontier classification

At the end, classify the Jacobsthal route as exactly one of:

## Outcome A — DIRECT LEVERAGE

An existing theorem/bound, possibly after finite verification, is genuinely strong enough to imply the anchored Legendre coprime escape for all positive `n`.

This outcome requires an actual inequality chain with constants and all finite exceptions discharged in principle.

## Outcome B — EXACT HARD-FRONTIER IDENTIFICATION

The route gives a mathematically exact and useful re-expression of the remaining provider as an anchored primorial coprime-gap problem, and possibly a stronger global Jacobsthal sufficient condition, but no known theorem reaches the required `2*n` scale.

## Outcome C — REDUNDANT REPACKAGING

The Jacobsthal vocabulary adds no useful distinction beyond the current support-wave/full-cover formulation and does not sharpen the statement of the remaining hard provider.

Do not choose Outcome A because the reformulation looks classical. The criterion is actual proof leverage.

---

# Q10 — next-step decision

Recommend exactly one of the following:

```text
1. stop Jacobsthal route; keep only the frontier identification
2. implement a thin DkMath theorem expressing the anchored coprime-gap equivalence
3. investigate one specific explicit Jacobsthal bound because it is numerically at the required scale
4. return to a different Primitive/Legendre route
```

If option 2 is recommended, specify the smallest theorem surface but do not implement it yet.

If option 3 is recommended, name the exact theorem/reference and show why its scale is plausibly sufficient before proposing another checkpoint.

---

# Existing DkMath files to inspect first

At minimum:

```text
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean
DkMath/NumberTheory/Primitive/PrimeWorldCardinality.lean
DkMath/NumberTheory/Primitive/EulerTotientBridge.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/Wave.lean
DkMath/NumberTheory/Legendre/Frontier.lean
```

Also inspect Mathlib for existing primorial/Jacobsthal-like definitions before inventing any vocabulary in the report.

---

# External reference discipline

External references are allowed for the classical Jacobsthal definition and known bounds.

For every externally sourced claim, record:

```text
author / title / theorem or page if identifiable
exact bound form
whether the constant is explicit
which parameter is used
whether the result is unconditional
```

Do not rely on blog-style summaries when a paper or standard reference is available.

Repository facts and literature facts must be clearly separated in the report.

---

# Non-goals

Do not in PRIM-JAC-000:

- modify Lean source;
- define a Jacobsthal function in DkMath;
- add a primorial abstraction;
- claim a proof of Legendre;
- claim `j(M(n)) ≤ 2*n` without a valid theorem;
- identify an anchored statement with a uniform all-interval statement;
- introduce PNT/Mertens/sieve estimates as implementation dependencies;
- add RH/CFBRC dependencies;
- use the RH branch as a provider;
- revive PRIM-PAR-001, PRIM-L024, or PRIM-FD-001;
- upgrade Lean/Mathlib.

---

# Verification

Because this is report-only:

```sh
git diff --check
```

and the usual whitespace / forbidden-placeholder audit are sufficient.

Do not run Lean builds solely for this checkpoint unless an existing source file is accidentally changed and must be restored/verified.

Report the final outcome and recommended next-step option explicitly.
