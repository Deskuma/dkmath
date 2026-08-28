# PUU-L034 — Successor-Pair Positive First-Hit / Adjacent Bad-Phase Isolation Audit

## 0. Status / purpose

PUU-L033 completed the anchor-seat exclusion audit with

```text
Outcome B — ANCHOR-SEAT-GAIN-COLLAPSES.
```

For the required finite bases, restricting arbitrary cyclic labels to square phases did not improve the **strictly forward** positive first-hit radius:

```text
S = {2,3}:   GenericPositiveRadius = SquarePositiveRadius = 4
S = {2,3,5}: GenericPositiveRadius = SquarePositiveRadius = 6.
```

Therefore square phase **alone** is closed as an independent positive-offset obstruction source.

The next checkpoint must add a genuinely independent coupling.  Use the exact successor relation already formalized in L010/L031:

```text
A_n     = n^2 mod M
A_(n+1) = (A_n + (2*n+1)) mod M.
```

Instead of asking how bad one square phase can be, ask whether **two consecutive square anchors can be bad simultaneously**.

This is still provider-side finite arithmetic.  Do not introduce a `2*n` shell width, Legendre consumers, primality claims, or generic Jacobsthal machinery.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairAudit
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetPositiveFirstHitAudit
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Successor-pair positive first-hit coordinate

Use the L033 positive first-hit coordinate

```text
H+(n) = squareAnchorFirstPositiveUnreservedOffset S n hS hSne.
```

Define the adjacent-pair coordinate by

```text
PairH+(n) = min (H+(n)) (H+(n+1)).
```

Suggested public definition:

```lean
noncomputable def squareAnchorSuccessorPairPositiveFirstHit
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  min
    (squareAnchorFirstPositiveUnreservedOffset S n hS hSne)
    (squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne)
```

Expose the semantic bounds:

```text
0 < PairH+(n)
PairH+(n) ≤ H+(n)
PairH+(n) ≤ H+(n+1)
PairH+(n) ≤ M.
```

The point is not the `min` definition itself, but the statement:

> within `PairH+(n)`, at least one of the two consecutive square anchors reaches a forward wheel survivor.

If convenient, expose this as a disjunction using the existing positive first-hit survivor theorem.

---

## 2. Threshold / bad-phase semantics

For a threshold `k`, expose the exact elementary equivalences

```text
k ≤ PairH+(n)
  ↔ k ≤ H+(n) ∧ k ≤ H+(n+1)
```

and/or

```text
PairH+(n) < k
  ↔ H+(n) < k ∨ H+(n+1) < k.
```

A named predicate is optional, for example

```lean
def SquarePositiveBadAt
    (S : Finset ℕ) (n k : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : Prop :=
  k ≤ squareAnchorFirstPositiveUnreservedOffset S n hS hSne
```

if it materially improves the API.

The mathematical interpretation should be explicit:

```text
pair radius gain
  = failure of adjacent anchors to be simultaneously bad at the same threshold.
```

Do not over-abstract this into a graph/dynamical system yet.

---

## 3. Successor-pair radius

Define the finite worst-case pair statistic over one old anchor period:

```lean
noncomputable def squareSuccessorPairPositiveFirstHitRadius
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).sup fun n =>
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne
```

Prove at least

```text
squareSuccessorPairPositiveFirstHitRadius S hS hSne
  ≤ squarePositiveFirstHitRadius S hS hSne.
```

Also expose periodicity in the anchor parameter if straightforward:

```text
PairH+(n + M) = PairH+(n).
```

Use existing same-phase / square-projection periodicity rather than reproving modular arithmetic from scratch.

---

## 4. Exact finite information-gain regressions

These regressions are part of the audit.  Use the public L033/L034 API rather than detached `decide` facts wherever practical.

### 4.1 `S = {2,3}`, `M = 6`

Required exact values:

```text
SquarePositiveRadius       = 4
SuccessorPairPositiveRadius = 1.
```

Every consecutive pair has one anchor whose positive first hit is `1`.

This is a strict gain:

```text
1 < 4.
```

### 4.2 `S = {2,3,5}`, `M = 30`

Required exact values:

```text
SquarePositiveRadius        = 6
SuccessorPairPositiveRadius = 5.
```

Provide a worst-pair witness, preferably `n = 11`:

```text
H+(11) = 6
H+(12) = 5
PairH+(11) = 5.
```

The square labels are

```text
11^2 mod 30 = 1
12^2 mod 30 = 24.
```

Thus the single-anchor worst case `6` does not persist across this successor edge, but the pair radius is still as large as `5`.

This is again strict information gain:

```text
5 < 6.
```

Do **not** infer a universal numeric bound from these examples.

---

## 5. Information-gain verdict

The checkpoint should end with an explicit audit verdict.

If the exact regressions above hold, preferred wording is:

```text
Outcome A — SUCCESSOR-PAIR-COUPLING-GAIN-FOUND
```

with the mandatory qualifier:

```text
FINITE STRICT GAIN, NO UNIFORM COVERAGE BOUND YET.
```

Meaning:

- L033 showed square phase alone gives no positive-radius improvement in the tested bases;
- L034 adds genuinely new information because the successor relation couples two square phases;
- in both required regressions, adjacent-pair coupling strictly reduces the worst positive first-hit statistic;
- this is **not yet** a theorem that the reduction is uniform over all finite prime bases, nor a consumer escape theorem.

If one of the required strict regressions fails in the implementation, record the exact result instead and do not force Outcome A.

---

## 6. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-successor-pair-positive-first-hit-audit-260828.md
```

The report should include:

1. pair coordinate definition;
2. threshold/bad-phase semantics;
3. pair radius and comparison with square positive radius;
4. exact `{2,3}` and `{2,3,5}` regressions;
5. the information-gain verdict;
6. a clear statement of what is still missing.

---

## 7. A+ rubric

A+ requires:

1. public successor-pair positive first-hit coordinate;
2. positivity / period bound / left-right bounds;
3. threshold semantics (`min` as simultaneous-badness test);
4. public successor-pair radius;
5. pair radius ≤ square positive radius;
6. `{2,3}` exact `1 < 4` regression;
7. `{2,3,5}` exact `5 < 6` regression with a worst-pair witness;
8. facade export and docstring;
9. report with explicit information-gain verdict.

---

## 8. STOP / non-goals

Do not introduce in PUU-L034:

- `SquareCell`, `SquareOffset`, `escapingSquareOffsets`, or Legendre consumers;
- a `2*n` shell-width bound;
- primality/compositeness of the first-hit seat;
- generic Jacobsthal / maximum-wheel-gap theory;
- asymptotic density, PNT, RH;
- PowerSwap / GN / CosmicFormula;
- prime powers;
- claims that successor-pair gain is uniformly strict for every basis unless actually proved;
- longer windows of three or more anchors before the pair audit is understood;
- graph abstractions that merely rename the finite `min` relation.

The checkpoint exists to answer one precise question:

> Does the **successor relation itself** add forward first-hit information that square phase alone did not provide?
