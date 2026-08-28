# PRIM-L060T — Terminal seat injection / disjoint support-cost closure

## Outcome

Outcome E — ENGINEERING BLOCK.

The terminal seat image surface was added, but the required next-seat
injectivity theorem could not be elaborated through the current cofactor API.
No concrete counterexample or terminal/collision-seat intersection was found.
The failed theorem was removed so that the checkout retains a compiling
surface.

## Implemented surface

`ParitySafeTerminalSupportCost.lean` now defines
`paritySafeTerminalFarProductSeats` as the image of
`paritySafeTerminalSurvivingFarProductKeys` under
`paritySafeFarProductWaveNextSeat`, together with the corresponding
`mem_paritySafeTerminalFarProductSeats` characterization.

The L060S terminal spine remains available: canonical residual-seat recovery,
the exact point equation, the ordered-prime packet, three-prime support
membership, support cases, and terminal support-card `3`.

## Injection attempt and blocker

The requested theorem
`paritySafeTerminalFarProductWaveNextSeat_injectiveOn` was attempted using:

1. canonical-owner equality to identify the first prime;
2. residual-seat transport to a common seat;
3. terminal point equality and the cofactor packet to derive cofactor `1`;
4. `paritySafeFarTripleCofactor_value_local_injective` to recover the ordered
   residual pair.

At the normal 200,000 heartbeat limit, elaboration timed out at `whnf`.  The
single theorem was then tried with the instruction-permitted local limit
`set_option maxHeartbeats 800000 in`; it still timed out at `whnf` after 112
seconds.  No global heartbeat option was changed.

Consequently, image-card equality, seat-side support transport, terminal
support cost, terminal/collision disjointness, and the combined single-sum
ledger were not added.

## Remaining boundary

The exact next step is to provide a thinner, separately compiled cofactor
normalization helper or otherwise reduce the injectivity theorem's elaboration
surface.  This checkpoint does not enter near counting, fourth-direction
fiber counting, fifth directions, new residual decomposition, generic unique
factorization, analytic estimates, descent, Legendre's conjecture, or RH.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed after removing the timed-out theorem.
- `lake build DkMath.NumberTheory.Legendre` passed with the facade import.
- The changed Lean source files contain no `sorry`, `admit`, `axiom`, or
  `native_decide`.
- No commit, push, PR, or CI action was performed.
