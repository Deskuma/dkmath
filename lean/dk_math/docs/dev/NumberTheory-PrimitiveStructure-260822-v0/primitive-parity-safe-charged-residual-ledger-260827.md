# PRIM-L061 — Charged residual normal form / weighted pair-overlap frontier

## Outcome

Outcome A+ — CHARGED RESIDUAL NORMAL FORM.

The accepted L060V support-charge ledger is now combined with the exact
pair-overlap and residual ledgers.  The resulting finite frontier is

```text
Near + 3*Terminal + DepthSeats + 4*Collision + Fourth
  <= PrimePairOverlap
  <= CoprimePrimePairOverlapCapacity.
```

## Implemented declarations

The new module
`DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger` provides:

- `paritySafeRechargeExactDepthFiberCollisionSeats_card_le_fiberExcess`;
- `exists_terminalCollisionSupportChargeSlack`;
- `exists_paritySafePrimePairOverlapCount_charged_normal_form`;
- `paritySafeChargedResidualWeight_le_primePairOverlapCount`;
- `paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount`;
- `paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_coprimePrimePairOverlapCount`.

The facade `DkMath.NumberTheory.Legendre` imports the new module.

## Proof boundary

The support charge is expressed using an existential nonnegative slack
`k`, avoiding a global natural-number subtraction definition.  The exact
normal form uses

```text
PairOverlap = SupportExcess + ResidualPairMass
ResidualPairMass = Near + Terminal + DepthSeats + FiberExcess + Fourth
SupportExcess = 2*Terminal + 3*Collision + k.
```

Since `CollisionSeats.card <= FiberExcess`, one unit of fiber excess is
absorbed into the collision coefficient, giving `+ 4*Collision` while the
depth-seat term already supplies the collision seat's base unit.

The L018 depth budget is not substituted into this lower-bound frontier; its
direction is an upper bound.  No new branch counting or contradiction is
claimed.

## Non-goals

Near product-wave counting, FourDirectionGate fiber counting, ExactFourth
strengthening, fifth direction, residual recursion, generic hypergraph APIs,
analytic estimates, descent, Legendre's conjecture, and RH remain outside
scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.
