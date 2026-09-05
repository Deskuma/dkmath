# PCK-005 — Finite square prime expansion implementation instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-006.md` / PCK-004

## 0. Authorization

Implement the first finite prime-world expansion operator for the Primitive
Conservation Kernel campaign.

The construction must use the canonical complete old world

```lean
primeScalesUpTo P
```

and identify new points only by support escape inside the certified square
window. Do not introduce `PrimeCompleteUpTo`, an arbitrary basis parameter,
or a new primality test.

The intended result is stronger and cleaner than a separate completeness
predicate:

```lean
squarePrimeExpansion P = primeScalesUpTo (squareBody P)
```

Thus one finite square expansion reconstructs exactly the canonical complete
prime world up to the square-Body endpoint.

## 1. Reuse audit

Before implementing, inspect and reuse:

```text
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean
```

Important existing surfaces:

```lean
primeScalesUpTo
mem_primeScalesUpTo
SupportDisjointFrom
supportDisjointFrom_primeScalesUpTo_iff

squareBody
squareBody_mono
prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody

prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
```

Use the exact final PCK-004 theorem name from the current source.

A repository search has found no existing `squarePrimeExpansion` operator.

## 2. Preferred owner

Preferred new file:

```text
DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean
```

Preferred namespace:

```text
DkMath.NumberTheory.Primitive
```

Import `SquareBody` and only the minimum additional Mathlib modules required
for `Finset.Icc` / filtering.

Do not enlarge `SquareBody.lean` with the operator unless source inspection
shows a concrete dependency reason. The square arithmetic owner should remain
separate from the finite-world expansion owner.

Do not modify a public aggregator in this checkpoint.

## 3. Canonical definition

Prefer the canonical complete-support operator:

```lean
/--
Extend the complete prime world at anchor `P` through its square Body.

The fresh part does not test primality directly. It keeps exactly the
nontrivial points in the square window that escape every old prime direction.
Square certification proves afterward that those escape points are prime.
-/
def squarePrimeExpansion (P : ℕ) : Finset ℕ :=
  primeScalesUpTo P ∪
    (Finset.Icc 2 (squareBody P)).filter
      (fun n => SupportDisjointFrom (primeScalesUpTo P) n)
```

Minor syntactic changes are acceptable if required by decidability/elaboration.

The lower bound `2` is intentional:
- it exposes `1 < n` immediately for square certification;
- old primes are supplied by the left union term;
- support-disjoint filtering does not need to inspect 0 or 1.

Do not use `Nat.Prime` in the fresh-part filter.

## 4. Required semantic theorem

Prove an exact membership theorem if it materially simplifies the final
equality. Preferred shape:

```lean
theorem mem_squarePrimeExpansion_iff
    {P n : ℕ} :
    n ∈ squarePrimeExpansion P ↔
      Nat.Prime n ∧ n ≤ squareBody P := by
  ...
```

This theorem may then be used to prove the canonical equality:

```lean
theorem squarePrimeExpansion_eq_primeScalesUpTo_squareBody
    (P : ℕ) :
    squarePrimeExpansion P = primeScalesUpTo (squareBody P) := by
  ext n
  rw [mem_squarePrimeExpansion_iff, mem_primeScalesUpTo]
```

Equivalent proof order is acceptable.

The equality theorem is the load-bearing result of PCK-005.

## 5. Forward direction: expansion member implies prime

There are two membership branches.

### 5.1 Old-world branch

If

```lean
n ∈ primeScalesUpTo P
```

then `Nat.Prime n` is immediate from `mem_primeScalesUpTo`.

Also prove

```text
n ≤ squareBody P
```

without adding a new global helper unless genuinely useful. Since a prime
member satisfies `2 ≤ n ≤ P`, the necessary endpoint inequality is
elementary from

```lean
squareBody P = P^2 + 2*P.
```

A short local `omega` / `nlinarith` / arithmetic proof is acceptable.

Do not introduce a general square-body lower-bound API merely for this branch.

### 5.2 Escape branch

If

```lean
n ∈ Finset.Icc 2 (squareBody P)
```

and

```lean
SupportDisjointFrom (primeScalesUpTo P) n
```

then use the already-existing square certification:

```lean
prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
```

The interval supplies `1 < n` and `n ≤ squareBody P`.

Do not re-run the minFac proof.

## 6. Reverse direction: every prime in the expanded range is generated

Assume

```lean
Nat.Prime n
n ≤ squareBody P
```

Split on `n ≤ P`.

### 6.1 If n ≤ P

Use

```lean
mem_primeScalesUpTo.mpr ⟨hnPrime, hnLeP⟩
```

and enter the left union branch.

### 6.2 If P < n

Enter the filtered escape branch.

Show:

```lean
n ∈ Finset.Icc 2 (squareBody P)
```

using primality for `2 ≤ n` and the assumed upper bound.

Then show:

```lean
SupportDisjointFrom (primeScalesUpTo P) n
```

For an old prime `r ≤ P` dividing the prime `n`, primality of `n`
forces the nonunit divisor `r` to equal `n`, contradicting `P < n`.

Prefer the existing exact membership bridge and standard `Nat.dvd_prime`
rather than factorization machinery.

No choice of a new prime witness is required.

## 7. PCK-004 connection

PCK-005's fresh filter is semantically stronger than a mere survivor set:
by PCK-004, every filtered point is a self-fresh direction.

If it is a short corollary and useful for documentation, one theorem of the
following shape MAY be added:

```lean
theorem freshPrimeDirection_self_of_mem_squarePrimeExpansion_freshPart ...
```

but this is optional and should not be added if the exact filter-membership
statement becomes cumbersome.

The required PCK-005 deliverable is the exact expansion/completeness equality,
not an additional FreshPrimeDirection wrapper.

## 8. Mathematical meaning

The operator implements the finite closure step

$$
\boxed{
\mathcal P_{\le P}
\longmapsto
\mathcal P_{\le (P+1)^2-1}
}
$$

because

$$
\operatorname{squareBody}(P)
=
P(P+2)
=
(P+1)^2-1.
$$

The construction itself uses only:
- the already-known complete old prime world;
- divisibility exclusion against that old world;
- the finite square bound.

Primality of each fresh escape point is a theorem consequence, not the
selection predicate.

This is the precise finite arithmetic realization of:

> old complete support + bounded conservation window + escape
> produces the next complete prime closure.

Do not state this as an unbounded prime-generation algorithm or as a claim
about computational efficiency.

## 9. Edge cases

The final theorem should preferably hold for all `P : ℕ`, including
`P = 0` and `P = 1`.

Do not add `2 ≤ P` merely to simplify proof engineering unless the
unconditional theorem genuinely becomes disproportionate. If an extra
hypothesis is required, report exactly why and treat it as a checkpoint
deviation requiring review.

The proposed `Icc 2 (squareBody P)` definition is chosen partly to keep
small-anchor behavior mathematically correct.

## 10. Firewalls

PCK-005 must not:

- define `PrimeCompleteUpTo` or equivalent;
- parameterize the operator by an arbitrary finite set `S`;
- use `Nat.Prime` in the fresh-part filter;
- introduce a sieve-performance claim;
- import PrimorialUniverse;
- implement the primorial coarse-anchor bridge;
- add the numeric 30 → 960 regression;
- add Gnomon resolution/projection theorems;
- import RH, zeta, Xi, PHZ, CFBRC, or analytic modules;
- add a generic `PrimitiveKernel` abstraction;
- use `sorry`, `admit`, `native_decide`, or a project axiom.

## 11. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Primitive.SquarePrimeExpansion
git diff --check
```

Run axiom checks on:

```text
mem_squarePrimeExpansion_iff
squarePrimeExpansion_eq_primeScalesUpTo_squareBody
```

Use exact final theorem names.

Audit the new module for forbidden imports and constructs.

If an existing source file is modified in addition to the new owner, build it
separately and justify the change.

## 12. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-007.md
```

Record:

- Outcome
- starting HEAD
- changed files
- exact operator definition
- exact membership theorem
- exact equality theorem
- old-world branch proof
- escape branch proof and reuse of square certification
- reverse prime-to-escape proof
- edge-case status for P = 0, 1
- whether PCK-004 is used directly or only supplies semantics
- focused build result
- `git diff --check`
- axiom/sorry audit
- next authorization

## 13. Next authorization

If PCK-005 is green, authorize only:

> PCK-006 — primorial coarse anchor → fine square world bridge.

PCK-006 should reuse:
- `finitePrimeBasisProduct` / synchronization from PrimorialUniverse;
- the canonical complete closure `primeScalesUpTo A`;
- PCK-003 coarse-to-fine certification;
- and, where useful, the PCK-005 expansion equality.

Do not implement PCK-006 in this checkpoint.
