# PUU-L036 — Successor-Pair Fresh-Prime Transport and Tied-Pair Obstruction

## Scope

This checkpoint is provider-side finite reservation arithmetic.  It combines
the successor-pair minimum from L034 with the single-anchor fresh-prime
transport from L035.  It introduces no `SquareCell`, `SquareOffset`, shell
width, Legendre consumer, Jacobsthal bound, analytic claim, or large primorial
scan.

The implementation is in
`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairFreshPrimeTransport`.

## Pair minimizers and persistence

For

```text
H0 = H⁺_S(n),  H1 = H⁺_S(n+1),  P = min H0 H1,
```

the module exposes `IsLeftPairMinimizer` and `IsRightPairMinimizer`.  Fresh
insertion is pointwise monotone:

```text
P ≤ P'.
```

The exact persistence criterion is:

```text
P' = P
↔
  (H0 = P ∧ ¬ q ∣ (n² + H0))
  ∨ (H1 = P ∧ ¬ q ∣ ((n+1)² + H1)).
```

Thus one surviving old minimizer is sufficient.  Its strict-delay dual is:

```text
P < P'
↔
  (H0 = P → q ∣ (n² + H0))
  ∧ (H1 = P → q ∣ ((n+1)² + H1)).
```

The proof derives these statements from the minimum semantics and the L035
single-anchor deletion law.

## Tied-pair obstruction

When `H0 = H1 = h` and insertion strictly delays the pair, the module proves

```text
q ∣ n² + h
q ∣ (n+1)² + h
```

and then subtracts the two raw seats to obtain

```text
q ∣ 2*n + 1.
```

The increment is therefore intrinsic to the consecutive-square pair; it is
not introduced as a shell-width assumption.

The contrapositive provider theorem is also exposed:

```text
H0 = H1 ∧ ¬ q ∣ (2*n+1) → P' = P.
```

The useful size specialization `2*n+1 < q → P' = P` is included as well.

## Untied boundary and regression

If `H0 < H1`, the left side is the unique old minimizer.  The corresponding
right-minimizer exclusion is formalized, documenting the boundary where a
single deleted seat can delay the pair without forcing divisibility of
`2*n+1`.  The symmetric case is covered by the pair persistence/strict-delay
criteria without introducing a second abstraction.

The visible regression is symbolic: it instantiates the tied-pair persistence
API with arbitrary finite prime basis, fresh prime, anchor, and tied first-hit
hypotheses.  A large numerical primorial expansion is intentionally not part
of this checkpoint.

## Verdict and branch closeout

**Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND.**

A fresh prime can strictly delay an equal-minimum successor pair only if it
also divides the intrinsic successor increment `2*n+1`.  This is provider
information beyond the one-anchor deletion law and is an obstruction seed.

The branch state is therefore:

```text
A. provider obstruction seed found, but no uniform coverage theorem.
```

The current first-hit/basis-growth route is closed at this finite-provider
boundary.  No claim is made that every pair is tied, that pair radii have a
uniform bound, that basis growth terminates, or that a Legendre conclusion
follows.

## Validation

Validated with:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairFreshPrimeTransport
```

The target completed successfully with 3024 jobs and no warnings from the
target module.
