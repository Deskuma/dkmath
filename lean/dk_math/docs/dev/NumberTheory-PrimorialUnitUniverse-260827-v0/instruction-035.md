# PUU-L035 — Fresh-Prime Positive First-Hit Persistence / Deletion-Delay Law

## 0. Status / purpose

PUU-L034 produced the first positive information-gain checkpoint after the square-phase-alone audits:

```text
Outcome A — SUCCESSOR-PAIR-COUPLING-GAIN-FOUND
```

The gain is finite and basis-specific.  The next question is not to add longer-window statistics immediately, but to understand how the positive first-hit geometry changes when the prime basis grows by one fresh prime.

Let

```text
M = finitePrimeBasisProduct S
H_S⁺(n) = squareAnchorFirstPositiveUnreservedOffset S n ...
```

and let `q ∉ S` be prime.  The old first-hit seat is

```text
x = n^2 + H_S⁺(n).
```

Since `x` is unreserved by `S`, enlarging the basis to `insert q S` can invalidate this old first hit for exactly one new reason: divisibility by `q`.

The intended transition law is therefore

```text
H_(insert q S)⁺(n) = H_S⁺(n)
  ↔ ¬ q ∣ (n^2 + H_S⁺(n)),
```

and if the fresh prime deletes the old hit,

```text
q ∣ (n^2 + H_S⁺(n))
  → H_S⁺(n) < H_(insert q S)⁺(n).
```

This is the first basis-growth theorem for the first-hit layer.  It should be proved semantically from reservation monotonicity and the fresh-prime insertion classification, not by finite computation.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFreshPrimeFirstHitTransport
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairAudit
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Generic fresh-prime reservation classification

Expose, if not already available in a sufficiently general public form,

```lean
reservedByPrimeBasis_insert_fresh_iff
    {S : Finset ℕ}
    {q x : ℕ}
    (hqS : q ∉ S) :
    ReservedByPrimeBasis (insert q S) x ↔
      ReservedByPrimeBasis S x ∨ q ∣ x
```

or an equivalent theorem with the necessary `hS` / `hq` assumptions.

Also expose monotonicity:

```lean
reservedByPrimeBasis_mono_insert
    ... :
    ReservedByPrimeBasis S x →
      ReservedByPrimeBasis (insert q S) x
```

and the non-reservation specialization when `x` is already unreserved by `S`:

```lean
not_reserved_insert_fresh_iff_of_not_reserved_old
    ...
    (hx : ¬ ReservedByPrimeBasis S x) :
    (¬ ReservedByPrimeBasis (insert q S) x) ↔ ¬ q ∣ x
```

Do not route these through Legendre or square-shell consumer APIs.

---

## 2. Positive first-hit monotonicity under basis growth

For a nonempty finite basis `S` and fresh prime `q`, prove pointwise

```lean
squareAnchorFirstPositiveUnreservedOffset_le_insert_fresh
```

with mathematical content

```text
H_S⁺(n) ≤ H_(insert q S)⁺(n).
```

Reason: every positive offset before `H_S⁺(n)` is already reserved by `S`, hence remains reserved after insertion.

Handle the different search periods correctly:

```text
old search:      1 ≤ t ≤ M
new search:      1 ≤ t ≤ q*M.
```

Do not silently assume the two periods are equal.

---

## 3. Exact persistence iff the old first-hit seat survives `q`

Main theorem:

```lean
squareAnchorFirstPositiveUnreservedOffset_insert_fresh_eq_iff
```

Preferred statement:

```text
H_(insert q S)⁺(n) = H_S⁺(n)
  ↔ ¬ q ∣ (n^2 + H_S⁺(n)).
```

Equivalent orientation is acceptable.

The forward direction should use the fact that the enlarged first-hit seat is unreserved by `insert q S`, hence not divisible by `q`.

The reverse direction should use:

1. the old first-hit seat is unreserved by `S`;
2. `q` does not divide it;
3. therefore it remains unreserved in `insert q S`;
4. every smaller positive offset was already reserved by `S`, hence remains reserved in the enlarged basis;
5. therefore the new minimum equals the old one.

This theorem is the checkpoint's core semantic result.

---

## 4. Deletion-delay theorem

Derive the strict branch:

```lean
squareAnchorFirstPositiveUnreservedOffset_insert_fresh_lt_of_dvd
```

with content

```text
q ∣ (n^2 + H_S⁺(n))
  → H_S⁺(n) < H_(insert q S)⁺(n).
```

Also provide the converse characterization if convenient:

```text
H_S⁺(n) < H_(insert q S)⁺(n)
  ↔ q ∣ (n^2 + H_S⁺(n)).
```

Do not claim a quantitative size of the delay yet.  The theorem only says whether the first hit persists or is pushed strictly forward.

---

## 5. Successor-pair basis-growth monotonicity

Using the pointwise single-anchor theorem, prove

```lean
squareAnchorSuccessorPairPositiveFirstHit_le_insert_fresh
```

with content

```text
PairH_S⁺(n) ≤ PairH_(insert q S)⁺(n).
```

Then lift this to the finite pair radii:

```lean
squareSuccessorPairPositiveFirstHitRadius_le_insert_fresh
```

with content

```text
PairRadius(S) ≤ PairRadius(insert q S).
```

The period changes from `M` to `q*M`; use the fact that the new supremum ranges over a larger period and contains the old `n < M` witnesses.  Reuse old-period periodicity where useful.

This is monotonicity of the absolute pair radius, not a theorem that the *gain* relative to the single-anchor radius is monotone.

---

## 6. Optional exact pair persistence criterion

If it remains concise, expose the local pair persistence law.

Let

```text
P = PairH_S⁺(n)
L = H_S⁺(n)
R = H_S⁺(n+1).
```

Then `PairH` remains equal after fresh-prime insertion iff at least one old minimizing side survives `q`:

```text
PairH_(insert q S)⁺(n) = P
  ↔
    (L = P ∧ ¬ q ∣ (n^2 + L)) ∨
    (R = P ∧ ¬ q ∣ ((n+1)^2 + R)).
```

An equivalent theorem split into sufficient / necessary directions is acceptable.

If both minimizing old sides are deleted, derive strict pair delay.

Do not over-engineer this section if the theorem becomes disproportionately complex; Sections 1–5 are the A+ core.

---

## 7. Required `30 → 210` regressions

Use

```text
S = {2,3,5}
M = 30
q = 7
insert q S = {2,3,5,7}
period = 210.
```

### Deleted old hit

At `n = 1`:

```text
H_30⁺(1) = 6
1^2 + 6 = 7
7 ∣ 7
H_210⁺(1) = 10.
```

This visibly exercises the strict deletion-delay branch.

### Persistent old hit

At `n = 11`:

```text
H_30⁺(11) = 6
11^2 + 6 = 127
7 ∤ 127
H_210⁺(11) = 6.
```

This visibly exercises the persistence branch.

### Basis-level pair audit

Also record, through public APIs where practical,

```text
PairRadius({2,3,5})   = 5
PairRadius({2,3,5,7}) = 7
```

and, if not too expensive,

```text
SquarePositiveRadius({2,3,5,7}) = 10
PairRadius({2,3,5,7})            = 7.
```

The last strict comparison shows the L034 successor-pair gain persists in this next primorial example, but **do not generalize it to all bases**.

---

## 8. Information-gain verdict

The checkpoint should end with one of:

```text
Outcome A — FRESH-PRIME DELETION-DELAY LAW FOUND
```

if the exact persistence/deletion classification is completed, or

```text
Outcome B — BASIS-GROWTH CLASSIFICATION INCOMPLETE
```

if only monotonicity is obtained.

Expected A-level interpretation:

```text
basis growth does not arbitrarily move the first hit;
it preserves the old first hit unless the newly inserted prime deletes that exact seat.
```

This is genuine provider information absent from L030's free-coordinate audit and L033's single-basis statistics.

---

## 9. STOP / non-goals

Do not introduce in L035:

- `SquareCell`, `SquareOffset`, `escapingSquareOffsets`, or Legendre consumers;
- a `2*n` shell-width bound;
- a claim that successor-pair strict gain persists for every prime basis;
- a quantitative universal bound on the deletion delay;
- generic Jacobsthal / maximum-wheel-gap machinery;
- PNT / RH / analytic sieve / asymptotic density;
- PowerSwap / GN / CosmicFormula;
- prime powers;
- longer successor windows;
- a claim that pair-radius gain is monotone under basis growth.

The purpose is to identify the **exact local mechanism** by which fresh-prime insertion changes positive first hits.

---

## 10. Report / completion criteria

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-first-hit-deletion-delay-260828.md
```

A+ requires:

1. generic fresh-prime reservation classification;
2. pointwise first-hit monotonicity under basis insertion;
3. exact persistence iff the old hit is not `q`-divisible;
4. strict deletion-delay theorem;
5. successor-pair pointwise monotonicity;
6. pair-radius basis-growth monotonicity;
7. `30 → 210` deleted/persistent regressions;
8. facade export + docstrings;
9. report with explicit information-gain verdict and non-goals.

The main research question is now:

> Can the exact fresh-prime deletion-delay law, combined with successor-pair isolation, eventually force a tower-level incompatibility among long positive reserved prefixes?

Do not answer that in L035.  First make the basis-growth transition exact.
