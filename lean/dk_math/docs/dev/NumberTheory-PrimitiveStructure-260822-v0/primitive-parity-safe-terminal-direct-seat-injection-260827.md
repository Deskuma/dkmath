# PRIM-L060U — Direct terminal support-key reconstruction / seat-card closure

## Outcome

Outcome A+ — DIRECT TERMINAL SEAT INJECTION.

The L060T cofactor-based injection blocker was bypassed using only the
compiled L060S exact three-support surface.  Equal terminal seats now recover
the same ordered terminal key, and the terminal seat image has the same card
as the terminal-key domain.

## Direct exact-support strategy

For two terminal keys with equal next seats:

1. the L060S prime packets identify both first primes with the same canonical
   support prime at that seat;
2. the second key's `q₂` and `s₂` are transported to the first key's seat;
3. `activeSupport_cases` places each transported prime among `p₁`, `q₁`, and
   `s₁`;
4. the two ordered inequalities are discharged by `omega`, leaving
   `p₁ = p₂`, `q₁ = q₂`, and `s₁ = s₂`.

No next-seat definition is unfolded in this proof.

## Implemented declarations

`ParitySafeTerminalSupportCost.lean` now contains:

- `paritySafeTerminalFarProductSeats` and its membership theorem;
- `paritySafeTerminalKeys_components_eq_of_nextSeat_eq`;
- `paritySafeTerminalKeys_eq_of_nextSeat_eq`;
- `paritySafeTerminalFarProductWaveNextSeat_injectiveOn`;
- `paritySafeTerminalFarProductSeats_card_eq_terminalKeys`.

The existing L060S support-card theorem and public docstrings remain intact.

## Cofactor boundary

The injectivity proof does not use
`paritySafeFarTripleCofactor_value_local_injective`,
`paritySafeFarTripleCofactor`, `paritySafeFarTripleCofactor_packet`, or any
`paritySafeFarProductWaveCofactor_*` theorem.  The earlier L060T `whnf`
timeout is therefore not reintroduced.

## Remaining boundary

This checkpoint intentionally stops before terminal support-cost inequalities,
terminal/collision-seat disjointness, and the combined disjoint-union ledger.
Near counting, fourth-direction counting, fifth directions, generic
factorization or hypergraph APIs, analytic estimates, descent, Legendre's
conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.
- No commit, push, PR, or CI action was performed.
