# PRIM-L060V — Terminal / collision disjoint weighted support-cost ledger

## Outcome

Outcome A+ — DISJOINT WEIGHTED SUPPORT-COST CLOSURE.

The terminal and exact-depth collision seat charges are now combined on one
candidate-side support-excess sum:

```text
2 * TerminalKeys.card + 3 * CollisionSeats.card <= SupportExcess
```

## Implemented surface

`ParitySafeFourDirectionGate.lean` now exposes
`paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate`, packaging
the existing L059 collision-seat witness and covered-candidate bridge.

`ParitySafeTerminalSupportCost.lean` adds:

- `paritySafeTerminalFarProductSeat_activeSupport_card_eq_three`;
- `paritySafeTerminalFarProductSeats_subset_candidate`;
- `paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats`;
- `paritySafeTerminalFarProductSeats_supportCost_sum_eq`;
- `three_mul_depthFiberCollisionSeats_card_le_localSupportCost`;
- `paritySafeTerminalCollisionSeats_union_subset_candidate`;
- `two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess`.

The terminal candidate proof uses the existing far-residual membership packet
and the candidate component of its underlying residual incidence.  The
terminal support card is transported from the L060S exact-three theorem.

## Proof architecture

The combined theorem uses one disjoint union of terminal seats and collision
seats.  Its summand is

```lean
fun r => (paritySafeActiveSupport n r).card - 1
```

The terminal sum is exactly `2 * TerminalSeats.card`, collision seats have
local cost at least three, and the union is a subset of
`squareAnchorOddPointCoprimeOffsets n`.  The terminal-seat/key-card equality
from L060U then gives the required key-side statement.  No independent
terminal and collision bounds are added together.

## Boundary

Near counting, FourDirectionGate fiber counting, ExactFourth strengthening,
the fifth direction, residual recursion, generic hypergraph APIs, analytic
estimates, descent, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.
