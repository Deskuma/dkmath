# GMPT-003 — Finite Petal primitive-transition paths

## Branch

```text
wip/number-theory-gnomon-multigauge-primitive-transition-260915-v0
```

## Context

GMPT-000/001 are implemented in this branch:

```text
DkMath.NumberTheory.MultiGauge.GnomonPetalTransition
DkMath.NumberTheory.Legendre.GnomonPetalTurnover
```

GMPT-002 is also now implemented:

```text
DkMath.Gnomon.PetalPrime
```

with the intended prime/atomicity bridge

```text
prime_oddGnomon_iff_petalAtom
odd_prime_existsUnique_gnomonAddress
```

The immediate next task is deterministic.  Do **not** open the Legendre capacity frontier yet.  Specialize the already existing generic `GNGaugePath` API to finite lists of genuine Petal transitions.

The core one-step transition is already production-shaped:

```text
P(a) -> P(petalMul a b)
```

with

```text
numerator   = oddGnomon b
denominator = 1
```

and balance supplied by

```text
oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b.
```

## Objective

Construct a canonical finite path

```text
P(a0)
  -> P(a0 ⋆ b1)
  -> P((a0 ⋆ b1) ⋆ b2)
  -> ...
```

from a start address `a0 : ℕ` and a factor list `bs : List ℕ`, using only existing `gnomonPetalTransition` steps.

The result must reuse `DkMath.NumberTheory.MultiGauge.Path`; do **not** introduce a second path framework.

## Preferred production home

Create:

```text
DkMath/NumberTheory/MultiGauge/GnomonPetalPath.lean
```

and expose it through:

```text
DkMath/NumberTheory/MultiGauge.lean
```

Keep Legendre out of this module.

## Required construction

Introduce the minimum helper API needed to describe the successive Petal addresses and transition list.  Naming may vary if a clearer existing convention is available, but the intended objects are approximately:

```lean
petalFold : ℕ → List ℕ → ℕ
petalPathTransitions : ℕ → List ℕ → List (GNGaugeTransition 2)
gnomonPetalPath : ℕ → List ℕ → GNGaugePath 2
```

A convenient recursion is:

```text
petalFold a []       = a
petalFold a (b::bs)  = petalFold (petalMul a b) bs
```

and each transition list step must literally be

```text
gnomonPetalTransition current b.
```

Prove the required `Linked` invariant rather than bypassing it.

Do not encode endpoint-copy coefficients.

## Required deterministic theorems

### 1. Start / endpoint identification

Prove the canonical start stage and endpoint stage facts, preferably with simp lemmas where appropriate:

```text
start = oddGnomonGaugeStage a
endStage = oddGnomonGaugeStage (petalFold a bs)
```

If the current privacy boundary of `Path.lean` makes the endpoint theorem awkward, add only the smallest reusable public path simp/cons lemma needed.  Do not duplicate `pathEndFrom` outside `Path.lean`.

### 2. Exact numerator / denominator support

For the canonical Petal path, prove:

```text
denominatorProduct = 1
numeratorProduct = product of oddGnomon over bs
```

For example the right-hand side may be represented by

```lean
(bs.map DkMath.Gnomon.oddGnomon).prod
```

or a small named helper if that materially improves proofs.

### 3. Exact endpoint observer / telescoping law

Derive, preferably from the generic `GNGaugePath.balance`, the exact observer identity

```text
(gnomonPetalPath a bs).endStage.value
  = oddGnomon a * product_{b in bs} oddGnomon b.
```

Also provide the equivalent address-level identity when useful:

```text
oddGnomon (petalFold a bs)
  = oddGnomon a * product_{b in bs} oddGnomon b.
```

Do not prove this by introducing a parallel arithmetic framework if the path balance plus existing Petal multiplication is sufficient.

### 4. Escape preservation under factor avoidance

Specialize `primeEscapes_all_stages`:

for prime `q`, if

```text
PrimeEscapes q (oddGnomonGaugeStage a)
```

and every factor address `b ∈ bs` satisfies

```text
¬ q ∣ oddGnomon b,
```

then `q` escapes at every stage of the canonical Petal path.

A useful endpoint corollary is also expected.

### 5. First/new capture localization to an actual Petal factor

Specialize the generic first-capture theorem.  If `q` escapes at the start but is captured somewhere in the canonical path, prove that there exists an actual factor address `b ∈ bs` such that

```text
q ∣ oddGnomon b.
```

For start-escape/end-capture, provide the corresponding endpoint corollary.

Prefer a theorem referring to an actual member of `bs`, not merely divisibility of the aggregate numerator product.

If straightforward, retain the stronger witness that the corresponding concrete transition is the escape-to-capture step; otherwise the factor-membership localization is the required checkpoint.

### 6. Small regressions

Add at least:

- empty path;
- one-factor path, reducing to `gnomonPetalTransition`;
- a two-factor path showing the endpoint observer is the product of three odd gnomons (start plus two factors);
- one prime-avoidance or capture-localization regression with small concrete addresses if `norm_num`/`decide` handles it cleanly.

Do not use `native_decide`.

## GMPT-002 documentation reconciliation

The current README/ROADMAP text is stale because `PetalPrime.lean` has already been implemented.

Update:

```text
README.md
ROADMAP.md
```

so that GMPT-000/001/002 reflect the actual validated state reached by this branch after builds pass.

In particular remove/replace wording such as:

```text
PetalAtom <-> prime until separately formalized
GMPT-002 — NEXT / DETERMINISTIC
```

Once this task builds, mark GMPT-003 appropriately as implemented/validated.

## Explicit non-goals

Do **not** claim or implement in this checkpoint:

```text
Legendre's conjecture;
prime existence in square intervals;
full-cover failure;
quantitative turnover capacity improvement;
arbitrary-degree primitive providers;
Norm/lattice landing extensions;
a new path framework;
new axioms.
```

Do not start GMPT-004 unless a strict numerical/cardinality gain falls out immediately from already proved theorems.  If only qualitative support localization is available, stop after GMPT-003 and report that boundary.

## Validation

Run focused builds first, then aggregators:

```text
lake build DkMath.Gnomon.PetalPrime
lake build DkMath.NumberTheory.MultiGauge.GnomonPetalTransition
lake build DkMath.NumberTheory.MultiGauge.GnomonPetalPath
lake build DkMath.NumberTheory.MultiGauge
lake build DkMath.NumberTheory.Legendre.GnomonPetalTurnover
lake build DkMath.NumberTheory.Legendre
```

Then run the repository-standard forbidden scan over changed production Lean files.  Required zero occurrences:

```text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
```

Run `#print axioms` for the principal new path theorems.  Expected dependencies are only the ordinary Lean/Mathlib logical foundations already accepted by DkMath; report the exact output.

Run `git diff --check`.

Do not label the checkpoint PRODUCTION-PROVED until these validations succeed.

## Deliverables

Create:

```text
report-003.md
validation-003.txt
```

The report must state:

1. exact files changed;
2. exact declarations added;
3. whether existing `GNGaugePath` was reused without duplication;
4. exact endpoint-product theorem obtained;
5. exact prime escape/capture localization obtained;
6. focused and aggregate build results;
7. forbidden scan result;
8. axiom audit result;
9. whether GMPT-004 received any genuine strict quantitative improvement.

Outcome classification:

```text
Outcome A — finite Petal path and factor-localized prime transport established
Outcome B — path composes but gives no factor-localized statement beyond aggregate support
Outcome P — engineering partial; deterministic target not fully compiled/proved
```

Prefer Outcome A only if the factor-membership localization theorem is actually present and validated.