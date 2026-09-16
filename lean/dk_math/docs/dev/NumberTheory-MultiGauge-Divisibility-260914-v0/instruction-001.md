# instruction-001 — MG-001 finite prime-escape paths

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Act as the production Lean implementer for the second Multi-Gauge checkpoint.

MG-000 is complete and approved. Do not redesign or refactor the two-stage kernel unless an actual proof obstruction is found.

This checkpoint generalizes the verified two-stage transport law to a finite path and proves where first prime capture can occur.

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/number-theory-multi-gauge-divisibility-260914-v0
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/README.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/CODEX.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-000.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-000.md
```

Inspect current source signatures before editing:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge.lean
```

Do not rely only on documentation summaries.

---

## Frozen MG-000 facts

The two-stage transition has

```text
second.value * denominator = first.value * numerator.
```

For prime `q`, production already proves:

```text
q | second.value
-> q | first.value OR q | numerator

q | first.value
-> q | second.value OR q | denominator

PrimeEscapes q first
q ∤ numerator
-> PrimeEscapes q second

PrimeEscapes q second
q ∤ denominator
-> PrimeEscapes q first

q ∤ numerator
q ∤ denominator
-> PrimeCaught q first <-> PrimeCaught q second

q ∤ numerator
q ∤ denominator
-> PrimeEscapes q first <-> PrimeEscapes q second.
```

Use these as the atomic transport lemmas.

Do not re-prove them from raw multiplication in every path theorem unless a small local proof is clearly simpler.

---

## Mathematical objective

Formalize a finite gauge chain

```text
A0 --(nu0,delta0)--> A1
   --(nu1,delta1)--> A2
   ...
   --(nu{k-1},delta{k-1})--> Ak
```

where each arrow is a `GNGaugeTransition d` and adjacent endpoints agree.

The central theorem must express:

```text
q escapes at A0
and q avoids every numerator
-> q escapes at every stage A0,...,Ak.
```

Equivalently:

```text
A prime can remain invisible through the whole finite gauge chain
until transition numerator support introduces it.
```

If it is eventually captured, localize a transition at which escape changes to capture and prove that `q` divides that transition numerator.

---

## Task 1 — minimal finite path representation

Add:

```text
DkMath/NumberTheory/MultiGauge/Path.lean
```

Choose the simplest representation that supports all required theorems.

Preferred shape:

```text
start : GNGaugeStage d
transitions : List (GNGaugeTransition d)
```

plus an adjacency / composability invariant ensuring that each transition starts at the current stage and the next transition begins at the preceding second stage.

A recursive `Linked` predicate, a small structure carrying a chain proof, or an equally simple equivalent is acceptable.

Avoid:

```text
custom automata
large Fin-indexed dependent state machinery
category-theory abstractions
graph infrastructure
```

unless a concrete Lean obstruction makes the simple `List` representation unusable.

The empty transition list should preferably represent a valid zero-step path containing only its start stage.

Expose stable helper APIs for at least:

```text
path start stage
path end stage
ordered stage list / stage membership, or an equivalent usable observer
transition list
```

Do not expose representation internals unnecessarily if a small semantic API is possible.

---

## Task 2 — path support products and telescoped balance

Define the finite transition support products, with names consistent with the final representation:

```text
numeratorProduct   = product of transition numerators
denominatorProduct = product of transition denominators.
```

Prove the composed balance law:

```text
end.value * denominatorProduct
=
start.value * numeratorProduct.
```

This theorem is a major MG-001 output, not merely an implementation detail.

It records exact multiplicative conservation of transition support across the finite gauge path.

For the zero-step path, both products should reduce naturally to `1` and the balance should reduce to reflexivity.

---

## Task 3 — global prime-support localization

For prime `q`, prove finite-path analogues of the MG-000 two-stage localization.

Required mathematical content:

```text
q | end.value
-> q | start.value OR q | numeratorProduct
```

and dually:

```text
q | start.value
-> q | end.value OR q | denominatorProduct.
```

Then export the useful corollaries:

```text
PrimeEscapes q start
q ∤ numeratorProduct
-> PrimeEscapes q end
```

and, if clean:

```text
PrimeEscapes q end
q ∤ denominatorProduct
-> PrimeEscapes q start.
```

Also prove capture / escape iff across the whole path when `q` avoids both total support products.

These may be proved from the telescoped balance or by induction from MG-000. Prefer the proof that gives the smallest and most maintainable theorem dependency graph.

---

## Task 4 — all-stage escape theorem

The endpoint theorem alone is not sufficient.

Prove that initial escape propagates through every intermediate stage when no transition numerator contains `q`.

Target semantics:

```text
Nat.Prime q
PrimeEscapes q path.start
(for every transition t in path, not q | t.numerator)
->
for every stage s occurring in the path,
PrimeEscapes q s.
```

This theorem is the direct formal answer to:

```text
How far can q keep escaping?
```

It keeps escaping through every stage until a numerator carrying `q` is encountered.

A formulation using an ordered stage list, membership, prefixes, or a recursive path predicate is acceptable. Keep it easy to use downstream.

---

## Task 5 — first-capture localization

Prove that if a prime begins escaped and becomes captured somewhere along the path, there is a transition where the status changes from escape to capture, and that transition numerator contains the prime.

Required semantic theorem shape:

```text
Nat.Prime q
PrimeEscapes q path.start
q is captured at some stage of path
->
exists transition t in path,
  PrimeEscapes q t.first
  AND PrimeCaught q t.second
  AND q | t.numerator.
```

The theorem does not need to expose a numeric minimal index if the existence of an actual escape-to-capture transition is proved.

This is preferred over decorative `Nat.find` machinery.

Also export the weaker but very reusable product-localization corollary:

```text
Nat.Prime q
PrimeEscapes q path.start
PrimeCaught q path.end
-> q | numeratorProduct.
```

If convenient, strengthen it to:

```text
exists transition t in path,
  q | t.numerator.
```

Do not claim uniqueness of the capture transition.

---

## Task 6 — optional dual disappearance theorem

Only if it follows with small symmetric proofs, add the denominator-dual statement:

```text
PrimeCaught q path.start
PrimeEscapes q path.end
->
exists transition t in path,
  PrimeCaught q t.first
  AND PrimeEscapes q t.second
  AND q | t.denominator.
```

and/or

```text
q | denominatorProduct.
```

This is useful but secondary to forward prime escape.

Do not let this optional symmetry delay the required MG-001 core.

---

## Task 7 — facade

Update:

```text
DkMath/NumberTheory/MultiGauge.lean
```

to import the new finite-path module.

Do not add ABC / FLT / Legendre / Norm dependencies.

Do not broadly modify `DkMath.lean` unless repository convention clearly requires it.

---

## Required regression examples

Add small theorem/example regressions sufficient to catch orientation mistakes in the transition support semantics.

At minimum include one finite path where:

```text
q avoids all numerators
-> escape persists,
```

or an abstract regression theorem instantiating a short path.

Also include a capture example or theorem demonstrating that a newly captured prime is found in numerator support.

Do not build a large numeric test harness.

---

## Non-goals

MG-001 must not implement:

```text
Norm divisibility
Eisenstein / TraceOne lattice landing
power/Core landing
Legendre application bridge
FixedBigGauge application bridge
ABC / FLT application bridges
asymptotic/counting arguments
an automaton state enum for boundary-only / GN-only / escape
```

The exact boundary/GN channel state machine is MG-002 and remains conditional.

---

## Proof discipline

```text
No sorry.
No admit.
No new axiom declarations.
No unjustified uniqueness theorem.
No hidden application-specific assumptions.
```

Reuse MG-000 theorems and standard `List`/divisibility lemmas.

If the proposed list representation becomes substantially more complex than the arithmetic being proved, stop and report the obstruction rather than building a large framework.

---

## Validation

Required focused builds from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.MultiGauge.Path
lake build DkMath.NumberTheory.MultiGauge
```

Also run:

```text
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
```

Record warnings or environmental messages separately from Lean failures.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-001.md
```

The report must contain:

```text
Outcome A / B / C
final path representation
files changed
path balance theorem
all-stage escape theorem
first-capture localization theorem
global numerator-product localization theorem
optional denominator dual results
theorem inventory
focused build commands and results
warnings / forbidden scan
any deviation from this instruction
whether MG-L2 Legendre audit is now justified
```

Outcome policy:

```text
Outcome A:
  finite path composition + all-stage escape + first-capture localization proved;
  MG-001 complete and MG-L2 review is justified.

Outcome B:
  path composition and endpoint transport proved,
  but exact intermediate / first-capture theorem needs a representation repair.

Outcome C:
  the chosen path abstraction obstructs even finite composition;
  stop and report rather than over-engineer.
```
