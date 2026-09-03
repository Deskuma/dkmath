# PCK-000 — Primitive Conservation Kernel reconnaissance

Date: 2026-09-03

Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`

Project roadmap:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/README.md
```

Expected report:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-001.md
```

## 0. Mission

PCK-000 is inventory-first.

Do not begin by creating a large new abstraction.

Determine exactly which parts of the following mathematical chain are already present in the current branch and which first adapters are genuinely missing:

```text
finite prime basis S
  ↓
finitePrimeBasisProduct S
  ↓
coarse anchor P
  ↓
complete prime support up to P
  ↓
squareBody P = P(P+2) = (P+1)^2 - 1
  ↓
escape from old support
  ↓
fresh prime / unique fresh direction
  ↓
coarse-to-fine transport q ≤ P
  ↓
half-unit / zero-conjugate depth coordinate
```

The primary aim is to avoid re-proving the substantial arithmetic already present in `SquareBody` and `PrimorialUniverse`.

## 1. Source of truth

Use the current branch tree as the source of truth.

Read at least:

```text
DkMath/CosmicFormula/CoreBeamGap.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/PrimorialUniverse/FinitePrimeSynchronization.lean
DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean
DkMath/NumberTheory/PrimorialUniverse/WheelSurvivor.lean
DkMath/NumberTheory/PrimorialUniverse/FreshPrimeLift.lean
DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/GNPrimeClosure.lean
```

Search all current `SquareAnchor*`, `PrimorialWheel*`, `PrimeComplete*`, `primeScalesUpTo`, `FreshPrimeDirection`, `SupportDisjointFrom`, and square-Body related declarations before adding any new definition.

## 2. Exact questions

### Q1. Existing complete-prime-support API

Determine whether DkMath already has a predicate equivalent to

```lean
∀ ⦃p : ℕ⦄, p ∈ S ↔ Nat.Prime p ∧ p ≤ P
```

or an existing canonical finite set exactly equal to all primes up to `P`.

Inspect especially `primeScalesUpTo P` and its membership theorem.

If this existing API is sufficient, do not introduce `PrimeCompleteUpTo`.

Record exact declarations and namespaces.

### Q2. Existing square-Body monotonicity

Search for an existing theorem equivalent to

```lean
q ≤ P -> squareBody q ≤ squareBody P
```

and/or

```lean
q ≤ P -> (q + 1)^2 ≤ (P + 1)^2
```

If absent, classify this as a minimal adapter candidate.

### Q3. Existing square escape theorem

Inventory the exact chain already available for

```text
m within squareBody P
+
not divisible by any prime ≤ P
⇒
Nat.Prime m
```

and for

```text
large prime divisor > P
⇒
unique fresh direction + old-generated cofactor.
```

Record theorem names, hypotheses, and whether they use:

```text
SupportDisjointFrom
primeScalesUpTo
PrimeScaleGeneratedBy
FreshPrimeDirection
```

Do not create semantic wrappers in PCK-000 unless one small wrapper is clearly necessary to expose an already-proved fact.

### Q4. Coarse primorial anchor interface

For finite prime basis `S`, inventory the exact API for

```text
finitePrimeBasisProduct S
common-period property
periodicity
survivor predicate
fresh-prime lift/refinement
```

Determine what is already sufficient to formalize the canonical regression

```text
{2,3,5} -> 30
```

without redefining a primorial function.

### Q5. Basis versus complete closure

Confirm that current APIs distinguish, or can distinguish without ambiguity:

```text
basis S = {2,3,5}
product/period = 30
all primes ≤ 30
wheel survivors modulo 30
```

These are not interchangeable.

In particular, do not claim that `gcd(n,30)=1` implies primality up to 960.

The intended two-stage closure is

```text
{2,3,5}
  ↓ product
30
  ↓ obtain/use complete prime support ≤ 30
all primes ≤ 30
  ↓ squareBody 30
primality certification through 960
```

PCK-000 must state exactly which arrow is already implemented and which is only a semantic composition of existing canonical APIs.

### Q6. Canonical `30 -> 960` theorem route

Find the shortest existing theorem chain proving the following mathematical statement:

```text
If 1 < m ≤ 960 and no prime p ≤ 30 divides m, then m is prime.
```

Prefer a generic theorem instantiated at `P = 30`, not a numeric special-purpose proof.

Record whether a new regression theorem would add value.

### Q7. Coarse-to-fine reuse

Determine the smallest theorem needed to obtain:

```text
q ≤ P
m ≤ squareBody q
support-disjoint from all primes ≤ P
⇒
Nat.Prime m
```

The expected proof should be a thin composition of square-body monotonicity and an existing square certification theorem.

If current APIs already prove it directly, report that instead.

### Q8. Half-unit zero-conjugate overlap

Search for existing definitions/theorems equivalent to

$$
\left(x-\frac q2\right)^2-\left(\frac q2\right)^2=x(x-q)
$$

and the corresponding zero roots / midpoint depth.

Inspect `CoreBeamGap`, square-difference modules, unit-coordinate modules, and existing Cosmic Formula examples before creating `HalfUnitZeroConjugate.lean`.

Classify one of:

```text
EXISTING-API-SUFFICIENT
THIN-ADAPTER-NEEDED
NEW-FOCUSED-MODULE-JUSTIFIED
```

### Q9. Primitive-kernel abstraction readiness

Do not implement a generic abstraction.

Only assess whether the following five ingredients already appear in multiple independent DkMath theorem families:

```text
known support
bounded conservation region
escape
fresh direction
refinement
```

At minimum compare:

```text
SquareBody / PrimorialUniverse
GN / GNPrimeClosure
Petal, if a direct structural correspondence exists
RH finite source only as future architecture, not as dependency
```

Classify generic abstraction readiness as:

```text
NOT-YET-JUSTIFIED
MULTIPLE-CONCRETE-FAMILIES-FOUND
```

with exact evidence.

## 3. Preferred outcome

PCK-000 should preferably be report-only.

If reconnaissance shows one truly minimal missing theorem that is useful for the next checkpoint, PCK-000 may add exactly one focused adapter module.

Good examples:

```text
squareBody_mono
coarse-to-fine square certification wrapper
```

Bad examples:

```text
new wheel implementation
new primality framework
new generic PrimitiveKernel class
new PrimeGauge
new RH bridge
```

## 4. Firewalls

1. Do not re-prove `squareBody_add_one_eq`.
2. Do not re-prove the minFac square argument if an existing `SquareBody` theorem already exposes it.
3. Do not redefine `primeScalesUpTo`.
4. Do not redefine `finitePrimeBasisProduct` or an equivalent primorial product.
5. Do not equate wheel survivor status with primality.
6. Do not use Legendre conjecture or RH.
7. Do not introduce a prime-existence assumption to make the closure work.
8. Do not introduce `sorry`, `admit`, new axioms, or `native_decide` as a proof shortcut.
9. Do not import RH modules into this NumberTheory campaign.
10. Do not claim that the project has generalized `Primitive` beyond primes until concrete cross-domain theorem families justify it.

## 5. Required report structure

Create `report-001.md` containing:

### 5.1 Repository state

- branch
- starting HEAD
- relevant current `develop` relationship
- files added/modified

### 5.2 Existing theorem inventory

Table columns:

```text
role
module
declaration
exact mathematical content
usable directly?
missing adapter, if any
```

### 5.3 Canonical square route

Write the exact current theorem chain for

$$
1<m\le P(P+2)
$$

plus complete old-prime exclusion implying primality.

### 5.4 Canonical `30` route

Record exact theorem instantiations for

$$
\{2,3,5\}\mapsto30,
$$

$$
30\cdot32=960,
$$

$$
960+1=31^2.
$$

Distinguish basis, period, complete support, and survivor set.

### 5.5 Coarse-to-fine gap

State whether square-Body monotonicity and the desired coarse-to-fine certification are already present.

### 5.6 Half-unit algebra gap

State whether the zero-conjugate quadratic already has a canonical owner or needs a new focused module.

### 5.7 Primitive abstraction audit

State whether generic abstraction is justified yet.

### 5.8 Classification

Choose one primary classification:

```text
PCK-CORE-ALREADY-MOSTLY-PRESENT
PCK-THIN-ADAPTER-LAYER-NEEDED
PCK-NEW-CORE-MODULES-NEEDED
```

Secondary classifications may include:

```text
COMPLETE-PRIME-SET-API-FOUND
SQUARE-BODY-MONOTONICITY-MISSING
COARSE-TO-FINE-WRAPPER-MISSING
HALF-UNIT-MODULE-JUSTIFIED
PRIMITIVE-ABSTRACTION-NOT-YET-JUSTIFIED
```

### 5.9 Next authorization

Authorize exactly one next checkpoint, normally PCK-001.

Do not authorize RH integration yet.

## 6. Verification

If report-only, run focused builds/checks on the load-bearing existing modules as practical, for example:

```text
lake build DkMath.NumberTheory.Primitive.SquareBody
lake build DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
lake build DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift
git diff --check
```

If a new adapter module is added, build it explicitly and record the result.

## 7. Success criterion

PCK-000 succeeds when PCK-001 no longer has to guess:

- what `30` means,
- where the complete prime support comes from,
- how square Body certifies primality,
- whether coarse-to-fine nesting already exists,
- whether the half-unit quadratic is new or already encoded,
- and which theorem is the actual first missing bridge.
