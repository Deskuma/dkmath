# PCK-004 implementation report

## Outcome

PCK-004 is implemented as the requested self-fresh square escape bridge.
Within a certified fine square-Body world, escape from the complete coarse
prime support first proves that the point m itself is prime, then packages
m as its own fresh prime direction.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
d060911394991b9bd4df9af7480546145d2e2a19
(docs(PCK): add PCK-004 self-fresh square escape instructions).
The worktree was clean at the start.

## Changed files

- DkMath/NumberTheory/Primitive/SquareBody.lean
  - Added only the self-fresh direction theorem.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-006.md
  - Added this implementation report.

No definition or structure was added. PCK-002 squareBody_mono, PCK-003
certification, FreshPrimeDirection, SupportDisjointFrom, public aggregators,
and all Gnomon, HalfUnit, prime-expansion, primorial, and analytic routes
were left unchanged.

## Final theorem

The exact theorem is:

    /--
    A support-disjoint point in a certified fine square world is not merely
    carrying some fresh prime divisor: square certification makes the point
    itself prime, hence the point itself is the fresh direction relative to the
    complete coarse world.
    -/
    theorem freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
        {q P m : ℕ}
        (hqP : q ≤ P)
        (hm : 1 < m)
        (hmUpper : m ≤ squareBody q)
        (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
        FreshPrimeDirection (primeScalesUpTo P) m m

Here q is the fine square anchor, P is the coarse complete-support anchor,
and m is both the escaping point and the fresh witness.

## Exact theorem reuse and proof route

First, the theorem reuses the PCK-003 adapter exactly:

    have hmPrime : Nat.Prime m :=
      prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
        hqP hm hmUpper hdisj

Next, support disjointness is applied to the self-divisibility fact:

    have hmNotMem : m ∉ primeScalesUpTo P :=
      hdisj hmPrime (dvd_refl m)

Finally, the existing constructor theorem is reused:

    exact freshPrimeDirection_of_prime_dvd_not_mem
      hmPrime (dvd_refl m) hmNotMem

The fresh witness is exactly m because PCK-003 proves Nat.Prime m, m
divides itself, and the same prime-divisor support hypothesis puts m outside
primeScalesUpTo P. No separate P < m theorem is needed.

## Distinction from generic support escape

The existing
exists_freshPrimeDirection_of_supportDisjointFrom theorem requires only
1 < m and support disjointness, and concludes that some fresh prime divisor
exists:

    ∃ p, FreshPrimeDirection S m p

PCK-004 does not duplicate or replace that generic theorem. Its stronger
conclusion comes specifically from the additional coarse-support and fine
square-Body hypotheses supplied to PCK-003:

    generic support escape -> some fresh prime divisor
    certified square escape -> m is prime -> m is the fresh direction

No existential wrapper or separate Nat.Prime conclusion was added.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.Primitive.SquareBody

Result: DkMath.NumberTheory.Primitive.SquareBody built successfully after
8668 jobs.

git diff --check passed.

The axiom check was run with:

    #print axioms
      DkMath.NumberTheory.Primitive.freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

Result: the theorem depends only on ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

No project-specific axiom, sorry, admit, or native_decide was introduced.
The modified source was audited for forbidden imports and constructs. It
does not import SquareGnomon, HalfUnitZeroConjugate, PrimorialUniverse, or
any analytic module, and it adds no new factorization or fresh-prime
mechanism.

## Boundary and next authorization

PCK-004 is green at the self-fresh square escape boundary. The generic
support-escape theorem remains the provider for arbitrary nontrivial
support-disjoint naturals; this checkpoint only collapses its witness to m
under the certified square-window hypotheses.

The next authorized checkpoint is PCK-005: finite square prime expansion.
It must reuse PCK-003 and PCK-004 and must not be implemented in this report.
