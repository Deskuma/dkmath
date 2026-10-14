# Instruction 006 — Legendre block support-excess localization / conservation

## Mission

Continue from Instruction 005.

Instruction 005 produced the first strict positive production-cost lower bound in the paused Legendre program.

Under the existing simultaneous full-cover hypothesis for successor shells 21 through 40,

    sum_{n=21}^{40} paritySafeSupportExcess n >= 38.

This was obtained from:

- exact lower cyclotomic persistence;
- fixed-prime shell addresses;
- fixed-seat divisibility q | 4*r+1;
- candidate parity, improving persistent reuse period from q to 2q;
- temporal persistence capacity improvement 169 -> 97;
- fresh lower incidence lower bound 148;
- mandatory first-slot capacity 110;
- fresh incremental support-excess charge 148 - 110 = 38.

The current unresolved frontier is no longer “do fresh incidences exist?” or
“does support excess become positive?”

It is:

> Where must this block support-excess mass go inside the existing
> pair-overlap / collision / residual ledger, and can that localization force a
> contradiction with current capacity?

The purpose of this task is to transport the checked block charge 38 into the
strongest existing Legendre cancellation frontier without inventing a parallel
ledger.

## Required source audit

Begin from the current production sources, at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeFreshCost
    DkMath.NumberTheory.Legendre.ParitySafePersistence
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
    DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
    DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate
    DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
    DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack

Audit exact theorem statements and definitions for:

    paritySafeSupportExcess
    paritySafePrimePairOverlapCount
    paritySafePairOverlapOutsideDepthCollision
    paritySafeDepthCollisionPairOverlapMass
    paritySafeDepthCollisionLocalSupportCost
    paritySafeRechargeExactDepthFiberCollisionSeats
    paritySafeRechargeExactDepthFiveDirectionCollisionSeats
    paritySafeLowCostResidualCapacity
    paritySafeRechargeExactDepthResidualPairCapacityExcess
    lowerParitySafeFreshSupport
    lowerParitySafeFreshExcessChargeCount
    lowerParitySafeFreshPair

Use the existing production objects whenever possible.

## Phase 1 — local excess-to-pair domination

At a seat with active support cardinality K, the existing production quantities satisfy

    support excess contribution = K - 1
    pair overlap contribution   = choose(K,2).

Prove the exact local comparison under the weakest honest assumptions.

Expected basic inequality:

    K - 1 <= choose(K,2)

for the relevant active-support cases.

Then lift this to actual candidate seats and shell totals:

    paritySafeSupportExcess n
      <= paritySafePrimePairOverlapCount n

if this is not already present.

Do not stop at a theorem that is already available under a different name.
Audit first, then add only the missing bridge.

## Phase 2 — exact pair-overlap localization

Use the existing exact decomposition

    paritySafePrimePairOverlapCount n
      =
      paritySafePairOverlapOutsideDepthCollision n
      +
      paritySafeDepthCollisionPairOverlapMass n.

Combine it with the collision identity

    paritySafeDepthCollisionPairOverlapMass n
      =
      paritySafeDepthCollisionLocalSupportCost n
      +
      collisionSeats.card
      +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n.

Derive the strongest direct bound of the shape

    paritySafeSupportExcess n
      <=
      outsideCollisionPairOverlap
      + collisionLocalSupportCost
      + collisionBaseline
      + depthResidualCapacity.

Then determine whether one or more of the latter terms can be eliminated or
absorbed using already-proved charging theorems.

The goal is to express support excess in the coordinate system already used by
the readable cancellation frontier.

## Phase 3 — block summation of the 38 charge

Transport the shellwise localization over the exact main block 21..40.

Target a theorem whose hypotheses are precisely the existing simultaneous
full-cover assumptions used in Instruction 005 and whose conclusion has a form
such as

    38 <=
      sum outsideCollisionPairOverlap
      + sum collisionLocalSupportCost
      + ...

The constant 38 must come from the checked production theorem from Instruction
005, not be reintroduced as a numerical assumption.

Prefer a generic block theorem first, with the N=20,T=20 statement as a
regression specialization.

## Phase 4 — exploit collision support-cost charging

Existing production already includes lower bounds such as

    3 * collisionSeats.card
      + fifthDirectionCollisionSeats.card
      <= collisionLocalSupportCost

or the exact current theorem of that form.

Use these to ask whether the collision-local share of the block excess can be
converted into existing positive LHS charges.

The desired structural split is morally:

    excess mass
      -> outside-collision pair mass
         OR collision-local support cost.

Then collision-local support cost itself should be interpretable through the
existing collision/fifth-direction charging API.

Do not assume every unit of excess creates a collision seat.
The localization must respect the actual support cardinality thresholds.

## Phase 5 — block readable frontier

The current readable shellwise frontier has the form

    2 * outsideCollisionPairOverlap
    + 11 * collisionSeats.card
    + 2 * fifthDirectionCollisionSeats.card
    + 3 * candidate.card
    <=
    3 * incidenceCount
    + 2 * lowCostResidualCapacity.

Sum this inequality across a finite block.

Then combine with:

    sum candidate.card + 38 <= sum incidenceCount

from Instruction 005.

Eliminate incidenceCount as strongly as possible.

The main research question is:

> Does the positive +38 charge survive algebraic elimination, producing a
> strictly stronger block inequality in terms of outside-collision mass,
> collision/fifth-direction charges, and low-cost residual capacity?

Do not treat a mere rescaling of the old inequality as a frontier gain.

A genuine gain should leave a new positive constant or strictly smaller RHS.

## Phase 6 — test contradiction on the main block

For N=20,T=20, kernel-compute every finite quantity that is already decidable:

- candidate-card sums;
- persistence capacities;
- fresh/excess lower bounds;
- outside-collision pair sums if reducible;
- collision-seat counts;
- fifth-direction collision counts;
- low-cost residual capacity sums;
- any other exact finite term entering the block frontier.

The primary test is whether the new block inequality is impossible numerically
under simultaneous full cover.

If yes, formalize the contradiction and conclude that the 20-shell simultaneous
full-cover hypothesis is false.

This would mean:

    not (forall i<20, SquareOffsetsFullyCovered (20+i+1)).

That is **not** yet Legendre's conjecture, but it is the first finite block
cover-failure theorem forced by the new machinery.

If no contradiction appears, record the exact slack.

## Phase 7 — from block failure to a Legendre-relevant witness

If the 20-shell simultaneous full-cover hypothesis is refuted, extract the
strongest immediate consequence:

    exists n in [21,40], not SquareOffsetsFullyCovered n.

Then use the existing equivalence between not-full-cover and square-anchored
support escape / prime existence in the corresponding square cell.

Audit exact existing theorem names before restating the result.

A successful consequence should be theorem-level and should not overclaim:

    exists n in [21,40], exists prime p with n^2 < p < (n+1)^2

or the exact interval convention already used by the Legendre package.

Only state this if the existing bridge supports it exactly.

## Phase 8 — generic block criterion

Whether or not the 20-shell block contradicts full cover, formulate a reusable
criterion.

Desired shape:

    if mandatory block support-excess charge
       > available block outside/collision/residual capacity,
    then not all shells in the block are fully covered.

Do not bake in the constants 20,20,38 unless the generic theorem is
unreasonably expensive.

A reusable finite-block contradiction principle would be more valuable than a
single numerical theorem.

## Phase 9 — identify the next frontier if no contradiction

If the readable block inequality remains feasible, determine exactly where the
remaining slack lives.

Possible recipients:

    outside-collision pair overlap
    collision local support cost
    low-cost residual capacity
    candidate/incidence slack
    unlocalized fresh first slots

Give one precise next theorem target.

Avoid vague statements such as “need stronger sparsity.”

## Possible outcomes

### Outcome A — finite block contradiction

The new 38 support-excess charge, after exact localization and block
cancellation, contradicts simultaneous full cover on at least one explicit
finite block.

This is a genuine Legendre frontier breakthrough, though not yet the global
conjecture.

### Outcome B — strict block frontier gain, no contradiction

The +38 survives into a strictly stronger readable block inequality, but the
main block still has positive slack.

Record the exact slack and the recipient term.

### Outcome P — exact localization, one quantitative bridge remains

Support excess is fully localized into the existing pair/collision ledger, but
one explicit inequality or injection is missing before the +38 can sharpen the
readable frontier.

Use Outcome P only if the missing theorem can be written precisely.

### Outcome C — current cancellation absorbs the charge

The existing algebraic cancellation causes the +38 to disappear completely,
showing that support excess alone is not the right conserved currency for the
next step.

If so, identify the quantity that survives cancellation.

## Non-goals

Do not claim or attempt by default:

    the full Legendre conjecture;
    an analytic prime estimate;
    asymptotic density;
    RH implications;
    FLT / ABC consequences;
    a new generic covering framework;
    replacement of the mature parity-safe ledger.

Do not introduce new axioms.

Do not use research endpoints carrying sorryAx in production proofs.

Do not infer a strict capacity improvement from numerical evidence alone.

## Implementation guidance

Prefer small extensions to existing Legendre modules where the theorem
naturally belongs.

If a new production module is justified, a suitable name is:

    DkMath/NumberTheory/Legendre/ParitySafeBlockLocalization.lean

Only create it if it contains genuinely reusable block mathematics.

Keep all main theorems phrased in existing production quantities.

Do not expose interpretation words such as “conservation”, “charge”, or
“escape” in public theorem names unless the formal statement makes them stable.

## Validation

For all new production declarations:

- focused builds for changed/new modules;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan on changed production Lean;
- #print axioms for every new public declaration;
- git diff --check.

All new production theorems must remain free of sorryAx.

## Durable checkpoint protocol

Update findings after:

- local K-1 vs choose(K,2) audit;
- shell support-excess -> pair-overlap bridge;
- pair-overlap -> outside/collision exact localization;
- block 38 localization;
- collision/fifth-direction transfer;
- readable block frontier elimination;
- N=20,T=20 exact numeric test;
- finite-block contradiction or exact slack;
- generic block criterion;
- final A/B/P/C decision.

Preserve failed inequalities and smallest counterexamples.

## Final report

Answer explicitly:

1. Is shell support excess always bounded by pair-overlap mass?
2. How exactly is that mass split between outside-collision and collision
   recipients?
3. Does the Instruction 005 lower bound 38 survive this localization?
4. Can collision-local support cost be converted into existing collision /
   fifth-direction charges?
5. What block inequality results after eliminating incidenceCount?
6. Is simultaneous full cover on shells 21..40 still numerically feasible?
7. If infeasible, what explicit square interval prime-existence consequence is
   obtained?
8. If feasible, where exactly does the remaining slack live?
9. Has the Legendre contradiction frontier moved strictly again?

End with exactly one judgment:

    Outcome A — FINITE BLOCK CONTRADICTION
    Outcome B — STRICT BLOCK FRONTIER GAIN, NO CONTRADICTION
    Outcome P — PRECISE LOCALIZATION BRIDGE REMAINS
    Outcome C — SUPPORT EXCESS IS ABSORBED BY CURRENT CANCELLATION
