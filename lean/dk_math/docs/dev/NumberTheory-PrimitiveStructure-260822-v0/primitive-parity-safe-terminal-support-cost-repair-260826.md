# PRIM-L060S — Active-support membership bridge / terminal exact-support closure

## Outcome

Outcome A — bounded checkpoint complete.

The L060R heartbeat repair was resumed at the requested smaller boundary.  A
definition-local membership bridge was added first, and the terminal support
cardinality then closed without a global heartbeat change or a combined
ledger.

## Implemented bridge

`mem_paritySafeActiveSupport_iff_dvd` now states, with `[simp]`, that

```text
q ∈ paritySafeActiveSupport n r
  ↔ q ∈ squareAnchorOddActivePrimes n ∧ q ∣ n ^ 2 + r.
```

It is located immediately after `paritySafeActiveSupport` in
`ParitySafeIncidenceBalance.lean` and compiles at the normal heartbeat.

## Terminal exact-support closure

`ParitySafeTerminalSupportCost.lean` now exposes:

- the terminal prime/order/canonical-owner packet;
- membership of the three ordered primes in the terminal active support;
- the arbitrary-support-member factorization cases
  `u = p ∨ u = q ∨ u = s`;
- lower and upper support inclusions and the resulting
  `activeSupport.card = 3` card sandwich;
- the `n = 16`, `r = 17` support-card regression.

The existing terminal residual-seat and exact point-equation spine remains
unchanged.  The proof uses the terminal identity
`n ^ 2 + r = p * q * s`, `Nat.Prime.dvd_mul`, and `Nat.dvd_prime`.

## Remaining boundary

This checkpoint does not add seat-image injectivity, key/seat injectivity,
disjointness, terminal support cost, or a combined global support-cost ledger.
Near branches, fifth directions, analytic estimates, descent, a global
contradiction, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source files contain no `sorry`, `admit`, `axiom`, or
  `native_decide`.

No commit, push, PR, or CI action was performed.
