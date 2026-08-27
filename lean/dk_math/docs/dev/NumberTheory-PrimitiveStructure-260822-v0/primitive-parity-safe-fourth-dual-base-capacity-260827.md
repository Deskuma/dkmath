# PRIM-L064 — Fourth gated dual-base capacity / LowCost closure

## Outcome

Outcome A+ — FOURTH GATED DUAL-BASE CAPACITY COMPLETE.

The exact fourth-direction branch now has the finite upper-control chain

```text
ExactFourth
  ⊆ FourthGateDualBase
  ⊆ ExactDualBase
  ⊆ PrimeAdmissible
  ⊆ OverAnchor.
```

Consequently,

```text
LowCostResidual
  <= NearWaveBudget
   + L018DepthBudget
   + FourthGateDualBase.card.
```

## Implemented module

The new module
`DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity` provides:

- `paritySafeFourthGateDualBasePairs`, with its membership theorem;
- `paritySafeRechargeExactFourthDirectionPairs_subset_fourthGateDualBase`;
- gated-universe inclusions into `ExactDualBase` and `PrimeAdmissible`;
- ExactFourth and gated-universe cardinal upper bounds;
- `paritySafeLowCostResidualCapacity`;
- the LowCost upper-control theorem using the gated Fourth capacity.

The public facade `DkMath.NumberTheory.Legendre` imports this module.
Module and public declaration docstrings record that this is an upper
capacity refinement, not an equality or an injectivity theorem.

## Proof boundary

The gated upper universe requires an existing prime-admissible pair together
with an existing `ParitySafeRechargeExactPairWitness` whose first prime lies
in `paritySafeFourDirectionGatePrimes`.  ExactFourth supplies these through
the existing exact-dual membership and L059 gate consumer.  The upper
universe intentionally does not require the selected-depth negation.

The result is an upper bound only.  It is not substituted into the L062
lower frontier

```text
LowCostResidual + 3*Terminal + 5*Collision <= PairOverlap.
```

In particular, no invalid inequality with `LowCostResidualCapacity` on that
lower-frontier left-hand side is introduced.

## Non-goals

FourthGate/ExactFourth equality, `Nat.minFac` global injectivity, recovery of
`(b,t)` from `(p,u)`, generic semiprime or 4-hypergraph libraries, fifth
direction, Fourth elimination, analytic estimates, descent, global
contradiction, Legendre's conjecture, and RH remain outside scope.

## Validation

- `lake build DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity`
  passed.
- `lake build DkMath.NumberTheory.Legendre` passed.
- `git diff --check` passed.
- Changed Lean source was checked for `sorry`, `admit`, `axiom`,
  `native_decide`, and global `maxHeartbeats` additions.
