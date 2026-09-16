# review-002 — GNIP-002 Collatz gnomon compatibility recovery

## Verdict

**APPROVED — Outcome A.**

GNIP-002 successfully makes `DkMath.Gnomon.Algebra` the source of truth for the application-independent odd-gnomon layer while preserving the existing Collatz public vocabulary and dynamics.

## Verified production changes

`DkMath.Collatz.GnomonEvaluation` now imports `DkMath.Gnomon.Algebra` and defines

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  DkMath.Gnomon.oddGnomon n
```

with the definitional compatibility theorem

```lean
@[simp] theorem oddGnomonLayer_eq_oddGnomon (n : ℕ) :
  OddGnomonLayer n = DkMath.Gnomon.oddGnomon n := rfl
```

The historical theorem names

```text
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
```

remain available, but their proofs are now sourced from the neutral gnomon layer.

## Collatz boundary preserved

The Collatz-specific API remains application-owned:

```text
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
RawGnomonRemainderAtDepth
FirstFailedPow2Depth
s / T / padicValNat bridges
```

No semantic change to the accelerated Collatz dynamics was introduced.

## Validation assessment

The reported successful builds

```text
lake build DkMath.Collatz.GnomonEvaluation
lake build DkMath.Collatz.Collatz2K26
lake build DkMath.Gnomon
```

are appropriate.  The missing `DkMath.Collatz` facade is not a GNIP-002 defect; using the existing downstream aggregate `DkMath.Collatz.Collatz2K26` is the correct compatibility check.

The pre-existing `sorry` warning in `ZsigmondyCyclotomicResearch.lean` is outside this checkpoint and does not invalidate the refactor.

## Mathematical consequence

The odd square shell now has one neutral source:

```text
DkMath.Gnomon.oddGnomon
```

with both application bridges:

```text
Collatz OddGnomonLayer  = neutral oddGnomon
neutral oddGnomon       = GTail 2 1 1 x
```

Thus the Collatz and Cosmic readings no longer duplicate the basic square-gnomon arithmetic.

## Next checkpoint

Proceed to **GNIP-003 — Legendre open unit-gnomon bridge**.

This checkpoint should not attempt the Legendre existence theorem.  Its job is to prove that the existing Legendre square-cell offsets are exactly the open interior of the unit square gnomon, at both predicate and finite-set levels, then restate the existing Legendre frontier in this vocabulary.
