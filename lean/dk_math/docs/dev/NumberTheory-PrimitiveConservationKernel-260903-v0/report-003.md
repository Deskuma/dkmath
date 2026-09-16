# PCK-002 implementation report

## Scope

This report records the implementation of PCK-002 from
instruction-003.md: the fine square-anchor monotonicity theorem. The
implementation is limited to the canonical owner
DkMath.NumberTheory.Primitive.SquareBody.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
2db1b7021468b0c6fe2c8e0812a940790e0b88fb
(docs(PCK): add PCK-002 squareBody monotonicity instructions).
The worktree was clean at the start.

## Changed files

- DkMath/NumberTheory/Primitive/SquareBody.lean
  - Added only squareBody_mono.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-003.md
  - Added this implementation report.

No change was made to the PCK-001 HalfUnit module, any public aggregator,
or any later primitive, prime, primorial, RH, PHZ, or CFBRC route.

## Implemented theorem

The final theorem is:

    /-- The natural square Body is monotone in its anchor. -/
    theorem squareBody_mono {q P : ℕ} (h : q ≤ P) :
        squareBody q ≤ squareBody P := by
      calc
        squareBody q = q * (q + 2) := by
          simp [squareBody]
          ring
        _ ≤ P * (P + 2) := by
          exact Nat.mul_le_mul h (Nat.add_le_add_right h 2)
        _ = squareBody P := by
          simp [squareBody]
          ring

The proof reuses the existing squareBody definition. It normalizes each
side to a product and applies natural-number product monotonicity from the
anchor inequality and its translated inequality. No helper theorem was
added, and squareBody_add_one_eq was neither re-proved nor refactored.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.Primitive.SquareBody

Result: DkMath.NumberTheory.Primitive.SquareBody built successfully
after 8668 jobs.

git diff --check passed.

The axiom check was run with:

    #print axioms DkMath.NumberTheory.Primitive.squareBody_mono

Result: the theorem depends only on propext. No project-specific axiom,
sorry, or admit dependency was introduced.

The modified source was audited for sorry, admit, native_decide, axiom,
and the PCK firewall topics. The new theorem contains none of these
constructs and introduces no import or aggregator change.

## Boundary and next authorization

PCK-002 is complete at the fine square-anchor monotonicity boundary.
This work does not establish a coarse-to-fine primality wrapper, prime
expansion, a primorial bridge, or any RH/PHZ consequence.

The next authorized checkpoint is PCK-003: the first thin coarse-to-fine
square certification adapter. PCK-003 is not implemented in this report.
