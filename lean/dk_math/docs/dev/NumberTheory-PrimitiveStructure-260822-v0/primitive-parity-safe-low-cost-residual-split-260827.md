# PRIM-L062 — Low-cost residual split / explicit collision weight five

## Outcome

Outcome A+ — LOW-COST RESIDUAL SPLIT COMPLETE.

Exact-depth seats are split into noncollision and collision seats, exposing
the effective collision weight five:

```text
LowCostResidual + 3*Terminal + 5*Collision <= PairOverlap
  <= CoprimePrimePairOverlapCapacity.
```

## Implemented module

The new module
`DkMath.NumberTheory.Legendre.ParitySafeLowCostResidualSplit` provides:

- `paritySafeRechargeExactDepthNonCollisionSeats` and its membership theorem;
- collision-seat subset of exact-depth seats;
- noncollision/collision disjointness, union, and exact card split;
- singleton-fiber semantics for noncollision seats;
- the noncollision L018 prime-square budget consumer;
- the explicit weight-five pair-overlap frontier and coprime-capacity version;
- `paritySafeLowCostResidualMass` and its pair-overlap/capacity bounds.

The public facade `DkMath.NumberTheory.Legendre` imports this module.

## Proof boundary

The depth-seat card identity is rewritten as

```text
DepthSeats = NonCollisionDepthSeats + CollisionSeats.
```

Combining this with the L061 frontier changes `4*Collision` to
`5*Collision`.  The depth-seat term already contains one collision-seat base
unit; the additional coefficient records the collision's charged support and
one fiber-excess unit.  The low-cost residual is exactly

```text
Near + NonCollisionDepth + Fourth.
```

The L018 depth budget is retained only as an upper-control consumer and is
not substituted into the lower frontier.

## Non-goals

Near counting, fourth-direction injectivity, ExactFourth strengthening, fifth
direction, residual recursion, generic hypergraph APIs, analytic estimates,
descent, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger`
  passed.
- `lake build DkMath.NumberTheory.Legendre.ParitySafeLowCostResidualSplit`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- The changed Lean source contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.
