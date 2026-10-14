# Instruction 005 — Legendre fresh-incidence cost / seat-local capacity Ultra exploration

## Mission

Continue from Instruction 004.

Instruction 004 moved the paused Legendre program from one-step support turnover to a finite-run temporal charging theorem:

- lower persistence is exactly the degree-2 homogeneous cyclotomic layer
  `Phi_2(n+1,n)=2*n+1`;
- an odd persistent prime q has ratio order 2;
- its shell addresses form one residue class modulo q;
- repeated persistence for the same q is spaced by multiples of q;
- a fixed persistent seat r additionally satisfies `q | 4*r+1`;
- finite-run persistent incidences admit a seat-weighted upper bound;
- simultaneous full cover therefore forces a nontrivial lower bound on fresh lower incidences;
- for N=20, T=20, at least 76 fresh lower incidences are required.

However, the current frontier did **not** move strictly because a fresh incidence need not create support excess, pair overlap, collision mass, or residual-capacity consumption.

This task asks:

> How many fresh lower incidences can be absorbed "for free" before the existing Legendre support/collision/residual ledger must pay a positive cost?

The objective is to classify fresh incidence cost and, if possible, convert the finite-run fresh lower bound into a strict reduction of an existing capacity term.

Do not assume that every fresh incidence is costly. Instruction 004 already kernel-checked a counterexample.

## Required source audit

Start from the current production sources, at minimum:

    DkMath.NumberTheory.Legendre.ParitySafePersistence
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
    DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
    DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
    DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
    DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate

Also audit the exact definitions of:

    paritySafeActiveSupport
    paritySafeSupportExcess
    paritySafePrimePairOverlapCount
    paritySafeLowCostResidualCapacity
    paritySafeRechargeExactDepthResidualPairCapacityExcess
    paritySafePairOverlapOutsideDepthCollision
    paritySafeDepthCollisionLocalSupportCost
    lowerParitySafeFreshSupport
    lowerParitySafeFreshCount
    lowerPersistentSeatPool
    lowerParitySafePersistenceCap

Do not invent a new cost ledger until the existing ones are fully mapped.

## Phase 1 — seat-local classification of fresh support

For a lower successor seat r at shell transition n -> n+1, inspect

    lowerParitySafeFreshSupport n r
      = paritySafeActiveSupport (n+1) r \ squareOffsetPrimeSupport n r.

Classify a fresh prime q according to the size and structure of the full successor support

    paritySafeActiveSupport (n+1) r.

At minimum distinguish:

1. **singleton fresh seat**
   the successor support has card 1 and the unique prime is fresh;

2. **multi-support fresh seat**
   the successor support has card >= 2 and at least one member is fresh;

3. **fresh-on-collision seat**
   the seat belongs to one of the existing exact-depth collision/fiber sets;

4. any existing low-cost / residual classifications already used by the production ledger.

The point is to discover whether "free fresh" has an exact existing meaning rather than introducing arbitrary terminology.

If a fresh singleton has zero `paritySafeSupportExcess`, formalize that exact relation.

If a fresh incidence on support size >=2 necessarily contributes to support excess or pair-overlap mass, prove the smallest honest theorem.

## Phase 2 — free-fresh capacity

Define a finite-run capacity only if it corresponds to an exact production class.

Candidate concept:

    freeFreshCount

= fresh lower incidences occurring at seats where the successor active support has no excess cost beyond the mandatory first support element.

Determine whether such incidences can be injected into an already bounded object, for example:

- lower successor candidate seats;
- singleton-support seats;
- first-prime / low-cost fibers;
- reduced quotient interval first occupants;
- terminal keys or an existing residual class.

The target is an upper bound

    total free fresh incidences over [N,N+T)
      <= B(N,T)

where B is either an existing capacity or a new finite expression strictly controlled by existing arithmetic data.

Do not accept the trivial bound by total candidate count unless it is enough to yield a strict net cost after subtracting from Instruction 004's fresh lower bound.

## Phase 3 — costly-fresh lower bound

Use the exact decomposition

    fresh = freeFresh + costlyFresh

or the correct existing analogue.

Derive

    costlyFresh
      >= freshLowerBound - freeFreshCapacity.

A successful theorem must use the actual `lowerParitySafeFreshSupport` / existing support ledger and not a duplicate abstract count.

If no exact disjoint split is natural, an inequality is sufficient:

    fresh <= freeCapacity + costlyLedgerMass.

The primary goal is to force some positive existing ledger mass from sufficiently many fresh incidences.

## Phase 4 — bridge to support excess

Audit whether a fresh incidence can be charged to

    paritySafeSupportExcess (n+1)

once the mandatory first active prime at the seat is removed.

A likely local shape to test is:

    number of fresh primes at seat r
      <= 1 + ((paritySafeActiveSupport (n+1) r).card - 1).

This inequality by itself is tautological if freshness is only a subset of active support. It is useful only if the first "1" can be globally bounded independently while the remainder is exactly support excess.

Therefore investigate a finite-run inequality of the shape

    totalFresh
      <= numberOfFreshOccupiedSeats
         + totalSupportExcessOnThoseSeats.

Then ask whether `numberOfFreshOccupiedSeats` has a strict seat-local capacity using the address constraints from Instruction 004.

This is a promising route because the checked counterexample with one fresh q and zero excess would consume the one free slot but no more.

## Phase 5 — bridge to pair-overlap

For support size k at one seat:

    choose(k,2)

is the local pair-overlap mass and

    k-1

is the local support-excess contribution.

Inspect whether multiple fresh primes, or one fresh prime added to persistent support, force a pair containing a fresh direction.

If useful, define a test-only or production object counting **fresh-involving pairs**:

    { unordered pairs in active support | at least one endpoint is fresh }.

Only add this to production if it yields an exact decomposition or strict inequality with the existing `paritySafePrimePairOverlapCount`.

Target relations could include:

    fresh-involving pair mass
      <= paritySafePrimePairOverlapCount,

or exact local identities in terms of persistent and fresh support cards.

A particularly useful exact combinatorial identity is:

    choose(P+F,2)
      = choose(P,2) + P*F + choose(F,2),

where P/F are local persistent/fresh cardinalities.

Investigate whether this identity exposes a new charge that Instruction 004 could not see.

## Phase 6 — seat-local arithmetic restriction

Exploit the new Instruction 004 constraint

    persistent q at seat r -> q | 4*r+1.

Transpose the temporal capacity from prime-weighted form to seat-weighted form where useful.

For fixed seat r, the possible odd persistent primes lie in the prime support of

    4*r+1.

Therefore the number of persistent prime labels at that seat is bounded by the number of distinct prime divisors of `4*r+1`.

Audit existing DkMath APIs for prime support/cardinality before defining a new `omega`-style function.

Try to prove a useful local bound:

    persistentSupport.card
      <= primeSupport(4*r+1).card.

Then combine with

    activeSupport.card
      = persistentSupport.card + freshSupport.card

to obtain a lower bound on fresh support when active support is large.

This route may connect naturally to support excess.

## Phase 7 — multi-shell seat charging

Instruction 004 bounded persistence by summing over primes q and their allowed seats.

Now try the dual viewpoint:

    fixed seat r
      -> allowed persistent primes divide 4*r+1
      -> only finitely many old directions can occupy the seat persistently.

Over a run of shells, determine whether repeated full cover at the same normalized seat sector forces replacement by fresh primes after the finite persistent-prime budget is exhausted.

Be careful: the candidate set and seat interpretation change with shell n. Do not identify unrelated seats across shells unless the production reindex provides the exact map.

If the current lower sector already uses the same offset r under canonical reindex, exploit that exact coordinate.

A successful multi-shell theorem may state that a fixed r can support persistence only from a finite prime set, with each q further restricted to one shell residue class modulo q.

## Phase 8 — interface with the existing cancellation frontier

The strongest current readable full-cover frontier includes:

    2 * paritySafePairOverlapOutsideDepthCollision n
    + 11 * collisionSeats.card
    + 2 * fifthDirectionCollisionSeats.card
    + 3 * candidate.card
    <=
    3 * paritySafeIncidenceCount n
    + 2 * paritySafeLowCostResidualCapacity n.

Determine whether fresh-cost information can strictly improve any term in this or the immediately preceding exact ledgers.

Possible strict gains include:

- replacing part of `paritySafeIncidenceCount` by a smaller persistence+free-fresh capacity;
- forcing a positive minimum `paritySafeSupportExcess`;
- forcing positive pair-overlap outside collision;
- reducing the usable `paritySafeLowCostResidualCapacity`;
- adding a new positive LHS charge justified by fresh-support combinatorics.

Do not call a theorem a frontier gain unless it produces a strict inequality or a new positive lower-bound term for at least one real finite instance.

## Phase 9 — finite calibration

Use N=20, T=20 as the main regression because Instruction 004 proved:

    full cover on all 20 successor shells
      -> total lower fresh incidences >= 76.

Compute or kernel-check the strongest available free-fresh capacity for this block.

The key diagnostic is:

    is freeFreshCapacity(20,20) < 76 ?

If yes, a positive number of costly fresh incidences is forced.

Then determine which existing ledger term must absorb those costly incidences.

If the answer is no, search for another finite block only as a diagnostic, not as proof of asymptotic behavior.

Record counterexamples to overly strong candidate inequalities as explicit regression theorems.

## Possible outcomes

### Outcome A — strict residual/collision frontier gain

Fresh-incidence cost is decomposed and the Instruction 004 finite fresh lower bound forces a positive amount of existing support-excess / pair-overlap / residual capacity. At least one current Legendre capacity frontier is strictly sharpened.

### Outcome B — exact fresh-cost decomposition, no strict gain

The free/costly structure and its connection to support-excess or pair-overlap is formalized, but the available free capacity is large enough that no current frontier term is strictly reduced.

### Outcome P — one precise capacity bridge remains

A positive costly-fresh lower bound is proved, but one explicit injection or inequality is still needed to place it into the existing residual/collision ledger.

Use Outcome P only if the missing theorem can be written exactly.

### Outcome C — fresh incidence is the wrong currency

Counterexamples show that even after seat-local and pair decomposition, fresh incidence does not control the current residual/collision ledger strongly enough to be a productive route. Identify the better conserved quantity.

## Non-goals

Do not claim or attempt by default:

    Legendre's conjecture;
    a prime between every consecutive pair of squares;
    analytic prime estimates;
    asymptotic density;
    FLT / ABC consequences;
    a new generic cover framework;
    wholesale refactoring of the mature parity-safe ledger.

Do not use existing sorryAx research endpoints in new production proofs.

Do not replace exact finite counting by numeric evidence.

## Implementation guidance

Prefer extending

    DkMath.NumberTheory.Legendre.ParitySafePersistence

only for direct consequences of its existing persistent/fresh split.

If a substantial new exact combinatorial layer is needed, use a small application-owned module such as

    DkMath/NumberTheory/Legendre/ParitySafeFreshCost.lean

but only if it contains actual reusable mathematics.

Reuse existing support-cardinality and pair-overlap definitions.

Avoid names like "free" or "costly" in public theorem APIs unless the formal definition is mathematically precise and stable. Prefer names such as:

    singletonFresh
    freshOccupiedSeat
    freshPairOverlap
    freshSupportExcessCharge

when these match the actual object.

## Validation

For every new production declaration:

- focused builds for changed/new modules;
- `lake build DkMath.NumberTheory.Legendre`;
- `lake build DkMath`;
- forbidden-token scan on changed production Lean;
- `#print axioms` for all new public declarations;
- `git diff --check`.

Keep new production declarations free of `sorryAx`.

## Durable checkpoint protocol

Update findings after:

- exact local fresh-support decomposition;
- identification of the zero-cost singleton mechanism;
- free-fresh capacity candidate;
- fresh/support-excess inequality;
- fresh-involving pair identity;
- seat-local `4*r+1` support bound;
- N=20,T=20 calibration;
- interface with the current cancellation frontier;
- final A/B/P/C decision.

Preserve failed inequalities and minimal counterexamples.

## Final report

Answer explicitly:

1. What exactly is a zero-cost fresh incidence in the current production ledger?
2. How many such incidences can a seat or finite shell block absorb?
3. What local identity relates persistent/fresh support to support excess?
4. What local identity relates them to pair-overlap mass?
5. Does `q | 4*r+1` give a strict seat-local persistence budget?
6. Does the 76-fresh lower bound for N=20,T=20 force any positive costly mass?
7. Which existing Legendre frontier term, if any, is strictly sharpened?
8. Has the full-cover contradiction frontier moved?

End with exactly one judgment:

    Outcome A — STRICT RESIDUAL/COLLISION FRONTIER GAIN
    Outcome B — EXACT FRESH-COST DECOMPOSITION, NO STRICT GAIN
    Outcome P — PRECISE CAPACITY BRIDGE REMAINS
    Outcome C — FRESH INCIDENCE IS THE WRONG CURRENCY
