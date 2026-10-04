# Instruction 004 — Legendre prime-persistence address bridge

## Mission

Reconnect the paused Legendre square-shell program to the new cyclotomic
prime-address machinery from Instructions 001–003.

The goal is **not** to prove Legendre's conjecture in this task.

The goal is to determine whether the exact adjacent-shell support-turnover law

    old support ∩ successor support
      = old support filtered by divisors of oddGnomon n

can be sharpened by interpreting the lower persistence channel through the
degree-2 homogeneous cyclotomic layer

    oddGnomon n = 2*n + 1 = Phi_2(n+1,n),

and then classifying, for a fixed prime q, the shell indices n at which q is
allowed to persist.

This is intended to attack the precise frontier recorded by the previous
Legendre campaign:

> exact turnover is known, but there is no quantitative charging principle
> turning simultaneous full cover into a lower bound on forced support changes
> or fresh incidences.

Instruction 003 supplies a new ingredient: a rational prime has a classified
cyclotomic layer address.  This task transposes that viewpoint from the
**degree axis** to the Legendre **shell axis**.

## Required source audit

Begin from the current production sources, at minimum:

    DkMath.NumberTheory.Legendre.GnomonSupportTurnover
    DkMath.NumberTheory.Legendre.GnomonPetalTurnover
    DkMath.NumberTheory.Legendre.Frontier
    DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
    DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
    DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
    DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation

and the new Gap Focusing / address stack from Instructions 001–003, especially:

    DkMath.NumberTheory.GapFocusing.HomogeneousAddress
    DkMath.NumberTheory.GapFocusing.PrimeOrder
    DkMath.NumberTheory.GapFocusing.CyclotomicAddress
    DkMath.NumberTheory.GapFocusing.CyclotomicBoundary

Reuse the existing homogeneous cyclotomic evaluator.  Do not create a second
definition of Phi_n(a,b) merely to fit the Legendre notation.

Record exact theorem names and types before adding bridge code.

## Phase 1 — degree-2 cyclotomic identification of the lower channel

Formalize, using the existing homogeneous evaluator, the exact identity

    Phi_2(n+1,n) = 2*n + 1 = oddGnomon n.

Prefer an element equality in the actual coefficient type rather than a norm or
cardinality comparison.

Then bridge it to the existing exact lower turnover theorem so that a common
old/successor prime q is characterized by:

    q ∈ old support
    and
    q | Phi_2(n+1,n).

Do not replace the existing support-turnover theorem.  Add the smallest useful
bridge theorem if it exposes genuinely new structure.

## Phase 2 — order-2 interpretation of an odd persistent prime

For an odd prime q satisfying the lower persistence condition

    q | 2*n + 1,

show the necessary coordinate nonvanishing facts modulo q and connect the
condition to the prime-order API from Instruction 003.

Target an honest theorem of the form

    q odd prime
    -> q | Phi_2(n+1,n)
    <-> primeOrder q (n+1) n = 2

under the exact hypotheses required by the production API.

If the theorem naturally states only one direction without an extra condition,
record the exact boundary rather than strengthening it cosmetically.

The intended interpretation is:

    lower persistent odd prime
      = a prime whose fundamental cyclotomic address for the ratio (n+1)/n
        is degree 2.

This interpretation must be theorem-backed before using it later.

## Phase 3 — shell-address classification for a fixed odd prime

Now fix an odd prime q and vary the shell index n.

Classify the set

    { n : Nat | q | oddGnomon n }.

The expected arithmetic progression is

    n ≡ (q-1)/2  (mod q),

equivalently

    n = (q-1)/2 + k*q

for some k, in the correct natural-number formulation.

Do not force this exact syntax if a residue-class theorem is cleaner in Lean.
The deliverable must make the periodic shell address explicit and reusable.

If useful, introduce a neutral predicate or finite-support helper for the shell
addresses of q, but avoid a new abstraction if the modular theorem itself is
enough.

This is the shell-axis analogue of Instruction 003's degree-axis address ray

    r, r*q, r*q^2, ...

and the two notions must remain distinct.

## Phase 4 — persistence spacing and lifespan

Derive exact consequences of the shell-address classification.

At minimum investigate and, if true, formalize:

1. **No consecutive lower persistence for an odd prime**

       q | oddGnomon n
       -> not q | oddGnomon (n+1).

   Equivalently, the same odd q cannot survive the lower common-support channel
   on two consecutive shell transitions.

2. **Exact spacing**

   If q divides oddGnomon n and oddGnomon m, then the shell-index difference is
   a multiple of q.

   Prefer a symmetric/congruence statement when it avoids subtraction issues.

3. **Finite interval frequency bound**

   Over a finite run of T shell transitions, bound how many indices can satisfy

       q | oddGnomon n.

   A bound equivalent to "at most one occurrence per residue class period q" is
   sufficient.  Use the cleanest Finset/cardinality formulation already
   available in Mathlib.

The first two are structural.  The third is the first potential ingredient for
a quantitative charging argument.

## Phase 5 — upper persistence channel calibration

The existing prime-threshold upper theorem says that, when n+1 is prime, every
old prime persisting through the upper channel is q=2.

Relate this to the new address language only if it produces a clean checked
statement.

A useful calibration is that q=2 has order-one base behavior and degree 2 is a
prime-power-inflated address, consistent with Instruction 003.

Do not spend the task building a large theory of the upper channel if this is
only a descriptive rephrasing.  The quantitative target remains the lower
persistent-prime channel.

## Phase 6 — persistence-capacity audit over multiple shells

This is the main research phase.

The previous Legendre campaign stopped because the exact one-step turnover law
did not yield a strict cardinality improvement.

Use the fixed-prime shell-address spacing to ask a new question:

> Over a block of consecutive shell transitions, how many persistent support
> incidences can the old prime basis actually sustain?

Investigate whether the existing Legendre support/capacity ledgers can consume a
bound of the shape

    total persistent odd-prime incidences
      <= sum over old primes q of shell-address-frequency(q).

Do not commit to this exact formula if the existing ledger counts a different
object.  Identify the actual production quantity first.

Candidate existing targets include:

    paritySafePrimePairOverlapCount
    paritySafeSupportExcess
    paritySafeLowCostResidualCapacity
    paritySafeRechargeExactDepthResidualPairCapacityExcess

but only modify or bridge to them if there is an exact containment, injection,
or inequality.

The decisive question is whether the new shell-address spacing gives a
**strictly smaller multi-shell persistence capacity** than the previous
one-step support filter.

A plain restatement

    persistent q -> q | oddGnomon n

is not progress; that theorem already exists.

## Phase 7 — fresh-incidence charging principle

If Phase 6 produces a genuine finite-run persistence bound, attempt the smallest
charging theorem connecting it to fresh incidences.

Research target:

    required cover incidences
      = persistent incidences + fresh incidences

or the correct existing analogue.

Then derive a lower bound of the form

    fresh incidences
      >= required incidences - persistence capacity.

The theorem need not prove Legendre.  A nontrivial lower bound that was
previously unavailable is sufficient to reopen the frontier.

Do not invent a new full-cover ledger if the current parity-safe ledger already
contains the needed counts.

If the current APIs prevent such a decomposition, identify the exact missing
bridge theorem.

## Phase 8 — relation to full-cover failure

Only if the previous phase yields a strict quantitative gain, test whether it
reduces an existing full-cover candidate balance or residual capacity term.

Possible outcomes:

### Outcome A — strict Legendre frontier gain

The shell-address law yields a new multi-shell persistence bound and a checked
fresh-incidence lower bound that strictly sharpens an existing Legendre
capacity/full-cover frontier.

This does not require proving Legendre itself.

### Outcome B — exact bridge, no strict capacity gain

The degree-2 cyclotomic / order-2 / shell-address bridge and persistence spacing
are all formalized, but after translation into the current Legendre ledger the
result is equivalent to or weaker than existing capacity information.

This is still a useful structural result.

### Outcome P — one precise quantitative bridge remains

The new shell-address theorem clearly gives a new persistence restriction, but
one explicit missing injection/identity/inequality prevents it from entering
the current full-cover ledger.

Use Outcome P only if the missing statement can be written as a compact
mathematical target.

## Important separation of axes

Keep the following two address mechanisms separate.

Instruction 003 degree axis:

    fixed (a,b,q), vary cyclotomic degree d
    q appears at d = r*q^k.

This Legendre task shell axis:

    fixed degree 2 and prime q, vary shell n
    q persists when n lies in one residue class modulo q.

A possible "moire" interpretation from superposing these axes is downstream
commentary only.  Do not use it as a theorem hypothesis or as evidence for a
capacity bound.

## Non-goals

Do not claim or attempt by default:

    Legendre's conjecture;
    a prime between every pair of consecutive squares;
    a full Bang-Zsigmondy theorem;
    FLT consequences;
    magic-square geometry;
    asymptotic prime distribution;
    analytic prime estimates;
    a wholesale rewrite of the existing Legendre package.

Do not derive element equality from norm equality.

Do not use existing research endpoints carrying sorryAx as production proof
dependencies.

## Implementation guidance

If the bridge deserves a production module, prefer an application-owned file
such as

    DkMath/NumberTheory/Legendre/CyclotomicPersistence.lean

or another small name matching the actual theorem content.

If only structural normalization is obtained, avoid decorative production
growth and record the result in the campaign report.

If a strict quantitative gain is found, keep the new capacity theorem as close
as possible to the existing Legendre ledger it sharpens.

Add regression examples where they clarify the distinction between:

    one-step turnover,
    fixed-prime shell spacing,
    multi-shell persistence capacity.

A useful calibration is q=3, where lower persistence occurs only at the
appropriate residue class and therefore cannot occur on adjacent transitions.

## Validation

For every new production theorem:

- run focused module builds;
- build DkMath.NumberTheory.Legendre;
- build DkMath.NumberTheory.GapFocusing if the bridge imports it;
- build DkMath;
- run repository-standard forbidden-token scans on changed production files;
- run #print axioms for all new public declarations;
- run git diff --check.

Expected new theorem dependencies must remain within the standard kernel
assumptions already accepted by the project.

## Durable checkpoint protocol

Update findings continuously after:

- source/API inventory;
- degree-2 homogeneous cyclotomic identity;
- order-2 bridge;
- shell-address residue-class theorem;
- no-consecutive / spacing theorem;
- finite-run frequency bound;
- Legendre ledger interface audit;
- any strict capacity gain or exact missing bridge;
- final A/B/P decision.

Preserve failed candidate inequalities if they explain why no strict gain is
available.

## Final report

Answer explicitly:

1. Is the lower Legendre persistence channel exactly a degree-2 cyclotomic
   layer?
2. For an odd persistent prime q, is its ratio order exactly 2?
3. What are the exact shell addresses of fixed q?
4. How far apart must repeated persistence events for the same q be?
5. What finite-run cardinality bound follows?
6. Does that bound strictly reduce an existing Legendre persistence/capacity
   quantity?
7. Does it force a new lower bound on fresh incidences?
8. Has the old Legendre stopping frontier genuinely moved?

End with exactly one judgment:

    Outcome A — STRICT LEGENDRE FRONTIER GAIN
    Outcome B — EXACT ADDRESS BRIDGE, NO STRICT CAPACITY GAIN
    Outcome P — PRECISE QUANTITATIVE BRIDGE REMAINS
