# PCK-003 implementation report

## Outcome

PCK-003 is implemented as the requested thin coarse-to-fine square
certification adapter. The proof composes the existing square-body
monotonicity theorem with the existing canonical finite prime-support
certification theorem.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
74f323dcf (docs(PCK): add PCK-003 coarse-to-fine certification instructions).
The worktree was clean at the start.

## Changed files

- DkMath/NumberTheory/Primitive/SquareBody.lean
  - Added only the new coarse-to-fine certification theorem.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-005.md
  - Added this implementation report.

No existing theorem statement, PCK-002 squareBody_mono, public aggregator,
Gnomon layer, HalfUnit layer, or later prime/primorial/analytic route was
changed.

## Final theorem

The exact theorem is:

    /--
    A complete prime support at a coarse anchor P certifies every fine
    square-Body world whose anchor q satisfies q ≤ P.
    -/
    theorem prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
        {q P m : ℕ}
        (hqP : q ≤ P)
        (hm : 1 < m)
        (hmUpper : m ≤ squareBody q)
        (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
        Nat.Prime m

The argument names preserve the semantic roles: q is the fine anchor and P
is the coarse anchor carrying the complete support.

## Exact proof composition

The proof is intentionally the two-step adapter:

    have hmUpperCoarse : m ≤ squareBody P :=
      hmUpper.trans (squareBody_mono hqP)
    exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
      hm hmUpperCoarse hdisj

Thus it uses only squareBody_mono and
prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody. No factorization,
minFac, wheel, CRT, GN, or Gnomon reasoning was added.

The canonical support remains primeScalesUpTo P. Its existing membership
theorem mem_primeScalesUpTo and semantic bridge
supportDisjointFrom_primeScalesUpTo_iff are reused indirectly by the
existing certification theorem. No new complete-support wrapper or
definition was introduced.

## Optional wrapper and deferred frontier

No raw-condition wrapper was added. The public surface remains solely the
canonical SupportDisjointFrom (primeScalesUpTo P) condition; a second raw
predicate would be redundant with the existing bridge.

The deferred frontier is PCK-004: square escape to the existing fresh-prime
direction surface, adding only the smallest missing semantic bridge if one
is genuinely absent. Prime expansion, primorial closure, the 30 to 960
regression, and all analytic consequences remain outside this checkpoint.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.Primitive.SquareBody

Result: DkMath.NumberTheory.Primitive.SquareBody built successfully after
8668 jobs.

git diff --check passed.

The axiom check was run with:

    #print axioms
      DkMath.NumberTheory.Primitive.prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

Result: the theorem depends only on ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

No project-specific axiom, sorry, admit, or native_decide was introduced.
The modified source audit found no newly added forbidden import or
construct. Existing FreshPrimeDirection declarations already present in
SquareBody were not modified or used by this adapter.

No optional raw wrapper, helper definition, or auxiliary structure was added.

## Boundary and next authorization

PCK-003 is green at the coarse-support to fine-square certification
boundary. It does not implement PCK-004, fresh-prime extraction, prime
expansion, primorial closure, or any RH, PHZ, zeta, Xi, CFBRC, or analytic
result.

The next authorized checkpoint is PCK-004: square escape to fresh prime
direction using the existing SquareBody and FreshPrimeDirection surface.
