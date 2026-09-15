# PCK-005 implementation report

## Outcome

PCK-005 is implemented as a finite square prime expansion operator. The
operator keeps the canonical complete old world and adds only support-escape
points in the finite square window. Its exact membership theorem shows that
the result is precisely the canonical prime world through the square-Body
endpoint.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
a280e97a60f72879a521f7c5dc27859224c475e7
(docs(PCK): add PCK-005 finite square prime expansion instructions).
The worktree was clean at the start.

## Changed files

- DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean
  - Added the finite expansion operator and its exact completeness theorems.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-007.md
  - Added this implementation report.

No existing source file was modified. In particular, SquareBody, PCK-003,
PCK-004, public aggregators, Gnomon, HalfUnit, PrimorialUniverse, and all
analytic routes are unchanged.

## Exact operator definition

The operator is the canonical old world plus the support-disjoint part of
the interval from 2 through squareBody P:

    noncomputable def squarePrimeExpansion (P : ℕ) : Finset ℕ := by
      classical
      exact
        primeScalesUpTo P ∪
          (Finset.Icc 2 (squareBody P)).filter
            (fun n => SupportDisjointFrom (primeScalesUpTo P) n)

The filter does not use Nat.Prime as a selection predicate. The
noncomputable declaration supplies the classical decidability required by
the support-disjoint proposition.

## Exact membership theorem

The first load-bearing theorem is:

    theorem mem_squarePrimeExpansion_iff
        {P n : ℕ} :
        n ∈ squarePrimeExpansion P ↔
          Nat.Prime n ∧ n ≤ squareBody P

The forward old-world branch obtains primality and n ≤ P from the existing
mem_primeScalesUpTo theorem, then proves P ≤ squareBody P by elementary
natural-number arithmetic. The forward escape branch reads 2 ≤ n and
n ≤ squareBody P from Finset.Icc and reuses
prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody. It does not
re-run the minFac proof.

For the reverse direction, a prime n below squareBody P is split by n ≤ P.
If n ≤ P, mem_primeScalesUpTo supplies the left union branch. If P < n,
the prime lower bound gives n ∈ Icc 2 (squareBody P). For any old prime
r dividing n, Nat.dvd_prime forces r = 1 or r = n; r ≠ 1 leaves r = n,
which contradicts n > P and old-world membership r ≤ P. This proves the
support-disjoint filter condition without factorization machinery.

## Exact equality theorem

The load-bearing finite closure result is:

    theorem squarePrimeExpansion_eq_primeScalesUpTo_squareBody
        (P : ℕ) :
        squarePrimeExpansion P = primeScalesUpTo (squareBody P)

It follows by extensionality from mem_squarePrimeExpansion_iff and the
existing mem_primeScalesUpTo theorem.

The theorem was also instantiated successfully at P = 0 and P = 1, so no
extra lower-bound hypothesis on P was introduced.

## PCK-004 connection and boundary

PCK-004 is not used directly in the proof term. The expansion uses the
existing square certification theorem directly, while PCK-004 supplies the
semantic interpretation that every filtered escape point is itself the
self-fresh prime direction. No optional fresh-direction wrapper was added.

The construction is a finite closure equality only:

    squarePrimeExpansion P = primeScalesUpTo (squareBody P)

It is not an unbounded prime-generation algorithm and makes no performance,
primorial, or prime-distribution claim. No PrimeCompleteUpTo-style wrapper,
arbitrary basis parameter, or new primality test was introduced.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.Primitive.SquarePrimeExpansion

Result: DkMath.NumberTheory.Primitive.SquarePrimeExpansion built
successfully after 8669 jobs, with no final Lean linter warnings.

git diff --check passed.

The axiom checks were run for:

    mem_squarePrimeExpansion_iff
    squarePrimeExpansion_eq_primeScalesUpTo_squareBody

Each reported only ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

The edge-case examples for P = 0 and P = 1 also compiled. The new module
was audited for forbidden imports and constructs. It imports only
Mathlib.Data.Finset.Interval and SquareBody, contains no sorry, admit,
native_decide, or project axiom, and does not import PrimorialUniverse,
SquareGnomon, HalfUnitZeroConjugate, or analytic modules.

## Next authorization

PCK-005 is green at the finite square prime-world expansion boundary. The
next authorized checkpoint is PCK-006: the primorial coarse-anchor to fine
square-world bridge, reusing the canonical closure and existing
PrimorialUniverse synchronization APIs. PCK-006 is not implemented here.
