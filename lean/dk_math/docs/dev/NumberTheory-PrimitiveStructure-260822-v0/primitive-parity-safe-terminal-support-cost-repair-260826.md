# PRIM-L060R — Terminal support proof decomposition

## Outcome

Outcome P — ENGINEERING PARTIAL.

The already-verified L060 terminal spine was retained.  The requested
heartbeat repair was attempted by splitting exact support into independent
theorems, but the first two mandatory support declarations still hit the
local elaboration budget:

1. `paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport`
2. `paritySafeTerminalSurvivingFarProductKey_activeSupport_cases`

Both were given a local `set_option maxHeartbeats 800000 in` annotation and
still timed out.  No mathematical counterexample was found.

## Verified spine

The module continues to prove:

- terminal key → rough selector → canonical far residual seat;
- `n ^ 2 + nextSeat = p * q * s` for next quotient `1`;
- the `n = 16`, `(3,(7,13))`, `nextSeat = 17` regression.

These are exposed in
`DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost` with public
docstrings and imported by the facade.

## Stopped boundary

Because `three_mem_activeSupport` and `activeSupport_cases` did not close,
the card sandwich, terminal seat cost, key/seat injectivity, collision
disjointness, and combined support-cost ledger were not added.  No
`sorry`, `admit`, axiom, or `native_decide` was used.

The next attempt should reduce the support-membership bridge itself—possibly
as a separately compiled theorem for active-support membership—before
reintroducing the three-prime cases theorem.  The exact Finset equality route
remains out of scope until the card theorem closes.

## Non-goals

Near branches, first-prime fiber counting, fifth directions, generic
factorization/hypergraphs, analytic estimates, descent, global contradiction,
Legendre's conjecture, and RH remain outside this checkpoint.

## Validation

`lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`,
`lake build DkMath.NumberTheory.Legendre`, and `git diff --check` pass after
restoring the last compiling partial surface.  The new Lean source is clean
of the prohibited tokens listed above.  No commit, push, PR, or CI action was
performed.
