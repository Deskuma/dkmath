# PRIM-L060 — Terminal support-cost checkpoint

## Outcome

Partial formalization / report boundary.  The terminal branch is now exposed
through a public residual-seat theorem and an exact terminal point theorem.
The exact active-support/cardinality theorem and the disjoint combined ledger
are not claimed in this checkout.

## Formalized

For a terminal surviving key `(p, (q,s))`, the module
`DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost` proves:

- the unique next seat belongs to the rough selector and is transported to a
  canonical far residual incidence;
- `n^2 + nextSeat = p*q*s` when the next quotient is `1`;
- the arithmetic regression `n = 16`, key `(3,(7,13))`, next seat `17`, and
  `16^2 + 17 = 3*7*13`.

The public facade imports the module.

## Explicit boundary

The remaining requested support theorem
`paritySafeActiveSupport n r = {p,q,s}`, its card consequence `= 3`, the
terminal support-cost inequality, terminal/collision disjointness, and the
single-sum combined inequality were not manufactured with `sorry` or an
axiom.  During implementation the generic exact-support declaration hit the
current Lean elaborator heartbeat boundary while reducing the existing
Finset/coercion-heavy support API.  This is an engineering/formalization
obstruction, not a mathematical counterexample; the next bounded step should
split that support proof into smaller public/local packets before attempting
the cost ledger.

The L059 FourDirectionGate first-prime fiber count and all analytic, descent,
near-branch, global-contradiction, Legendre, and RH claims remain out of scope.

## Validation

`lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost` and
`lake build DkMath.NumberTheory.Legendre` both pass.  `git diff --check` passes,
and the new Lean source has no `sorry`, `admit`, `axiom`, or `native_decide`.
No commit, push, PR, or CI action is part of this checkpoint.
