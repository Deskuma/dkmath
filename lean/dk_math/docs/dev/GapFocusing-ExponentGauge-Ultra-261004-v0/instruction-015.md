# Instruction 015 — Legendre CrossFiber quotient routing / composite conservation

## Mission

Continue from Instruction 014.

Instruction 014 completed the sqrt-rough factorization census:

    R = U + Cube + Cross + Repeated + Triple,

with exact bijections for all four covered arithmetic types.

The singleton cross-semiprime contribution is now explicit:

    Cross = sum over p in roughActiveLabels(n,sqrt n)
              |sqrtRoughCrossFiber(n,p)|,

where

    sqrtRoughCrossFiber(n,p)

is exactly the prime-above-anchor filter of the existing reduced quotient interval.

The current geometric and active-wave upper bounds are too coarse when summed over p.

The next task is therefore not another raw interval bound.

The objective is:

> split each owner-p quotient window into prime and composite quotients, then route the composite part back into the already-proved Cube / Repeated / Triple factorization census.

If successful, Cross becomes the residue after subtracting structurally classified composite quotient mass from an exact finite quotient carrier.

No new excess, support, moment, or uncovered ledger should be introduced.

## Core picture

For a fixed sqrt-rough owner prime p, consider quotient values q with

    n^2 < p*q <= n^2+2n,

and the existing reduced/coprime/parity conditions.

The prime-above-n values are exactly CrossFiber.

The complementary quotient values should be classified arithmetically.

The intended conservation picture is:

    QuotientCarrier(n,p)
      = CrossFiber(n,p)
        disjoint union
        CompositeRoutedFiber(n,p)
        disjoint union
        any explicitly identified non-cross prime classes.

Do not assume this exact shape before auditing endpoints and q<=n prime quotients.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughSingleton
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughStrata
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughProductWaves
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount
    DkMath.NumberTheory.Legendre.Wave

and any current Mathlib APIs for:

- factorization/minFac;
- prime versus composite natural-number partition;
- exact finite interval splitting;
- image/fiber cardinality;
- quotient/remainder endpoint arithmetic.

Record exact theorem names before extending production.

## Phase 1 — define the exact owner-p quotient carrier

For p in `roughActiveLabels n (Nat.sqrt n)`, define the finite quotient window that retains the same endpoint arithmetic as the cross fiber but does not impose primality.

Preferred carrier:

    sqrtRoughQuotientFiber n p

with membership equivalent to

    n < q,
    n^2 / p < q,
    q <= (n^2+2n)/p,

plus exactly the reduced quotient conditions actually needed to make

    r = p*q - n^2

an odd/coprime candidate.

Do not silently use all integers in the Ioc if reduced quotient conditions remove some.

Reuse `paritySafeReducedQuotientInterval` if that is the exact owner-p carrier.

## Phase 2 — exact CrossFiber filter

Prove:

    sqrtRoughCrossFiber n p
      = sqrtRoughQuotientFiber n p filtered by Nat.Prime

or, if q>n must remain explicit, by

    q.Prime and n<q.

This should refine/reuse

    sqrt_cross_fiber_eq_reduced_quotient_filter.

Do not introduce a second equivalent cross definition unless it improves later partition proofs.

## Phase 3 — prime/composite partition

Define the complementary composite quotient fiber:

    sqrtRoughCompositeFiber n p

as quotient-carrier elements q with q not prime.

Because q>n>=1 in the intended scope, q is neither 0 nor1. Prove the exact disjoint partition:

    QuotientFiber = CrossFiber union CompositeFiber,

and

    card QuotientFiber = card CrossFiber + card CompositeFiber.

If q<=n prime values remain in the chosen carrier, split them into a third explicitly named class rather than hiding them.

## Phase 4 — quotient-to-seat map

Map each quotient q in the owner-p carrier to

    r = p*q - n^2.

Prove the exact seat packet available from the quotient hypotheses:

- SquareOffset n r;
- Coprime(2*n, n^2+r);
- n^2+r = p*q;
- p belongs to actual support;
- r belongs to the appropriate sqrt-rough carrier exactly when all prime divisors of q exceed sqrt n.

Do not assume singleton support for composite q.

## Phase 5 — classify composite quotient prime factors

For q in the composite fiber, use a prime divisor u of q.

Since

    n^2+r = p*q

and r is sqrt-rough, every prime divisor of q must exceed sqrt n.

Classify whether those prime divisors are:

- <=n and therefore active support labels;
- >n and therefore external factors.

Use Instruction 014's factorization census to determine which combinations are actually possible inside the shell.

## Phase 6 — expected composite quotient routing

Test and prove the strongest correct routing theorem.

Expected cases for composite q are:

1. q = p^2, corresponding to Cube point p^3;
2. q = p*a or q = a^2 for an active a != p, corresponding to Repeated points;
3. q = a*b for distinct active a,b != p, corresponding to Triple points;

subject to sorted-owner conventions and possible multiplicity/orientation issues.

Audit carefully whether the owner p must be:

- the least active support label;
- any one of the support labels;
- or the unique singleton owner only in the Cross case.

Do not force a false one-owner routing.

Preserve the smallest counterexample if a composite quotient belongs to more than one p-owner fiber.

## Phase 7 — multiplicity of routing by factorization type

This is essential.

A Repeated or Triple seat may appear in several owner-p quotient fibers because each active support prime can be chosen as p.

Determine the exact multiplicity:

- Cube p^3: how many owner fibers contain quotient p^2?
- Repeated p^2*q / p*q^2: how many owner fibers and which quotients?
- Triple p*q*s: how many owner fibers?

Expected raw multiplicities are related to support size, but prove them from the quotient carrier.

Do not subtract composite counts from summed quotient capacity until this multiplicity is exact.

## Phase 8 — global quotient conservation

After multiplicity is established, sum owner-p quotient-cardinalities over

    roughActiveLabels n (Nat.sqrt n).

Seek an exact identity of the form

    TotalQuotients
      = Cross
        + cCube*Cube
        + cRepeated*Repeated
        + cTriple*Triple,

with explicit natural coefficients justified by owner multiplicity.

Do not guess coefficients.

If there are endpoint or prime-q<=n classes, retain them as explicit terms.

This is the first main target of Instruction015.

## Phase 9 — relation to rough incidence / moments

Compare the coefficients in the quotient conservation law with:

    roughI = Cube + Cross + 2*Repeated + 3*Triple,

    M2     = Repeated + 3*Triple,

    M3     = Triple.

Determine whether `TotalQuotients` is already equal to one of the existing currencies or to a simple linear combination.

If so, prove the identity rather than keeping duplicate terminology.

The ideal outcome would expose Cross by exact subtraction from a known quotient total and already-counted product types.

## Phase 10 — exact owner-p quotient cardinality

For prime anchors, derive an exact floor/carry expression for

    |sqrtRoughQuotientFiber n p|.

Reuse the reduced quotient interval and parity/anchor corrections.

Do not merely restate the coarse bound

    floor(2n/p)+1.

Preserve endpoint carries exactly.

If the quotient carrier is exactly an existing reduced quotient interval slice above n, prove that exact cardinality formula.

## Phase 11 — separate above-n and below-or-equal-n quotient mass

Audit the full reduced quotient interval for owner p.

Decompose it at q=n:

    q<=n
    versus
    q>n.

Interpret q<=n through existing active support/product census where possible.

Interpret q>n as:

    prime external Cross
    or composite external/cofactor routing.

This split may be more useful than prime/composite alone.

## Phase 12 — composite quotient normal forms

For each factorization census type, prove the exact quotient observed from each supported owner.

Examples to verify:

    point=p^3:
      owner p -> quotient p^2;

    point=p^2*q:
      owner p -> quotient p*q,
      owner q -> quotient p^2;

    point=p*q*s:
      owner p -> quotient q*s,
      owner q -> quotient p*s,
      owner s -> quotient p*q.

These are examples, not assumptions about which values survive the q>n filter.

Record which quotient values are >n and hence enter the target quotient carrier.

## Phase 13 — q>n multiplicity refinement

The owner multiplicity in the above-n quotient carrier may be smaller than support size.

For each census type, determine exactly how many owner quotients satisfy q>n.

This is likely the key refinement.

For example, in a triple point p*q*s near n^2, some complementary pair products may exceed n while others may not.

Define, if useful, a finite `largeComplementCount` attached to each Repeated/Triple key.

Then prove a global exact identity:

    TotalAboveNQuotients
      = Cross
        + sum over RepeatedKeys largeComplementCount
        + sum over TripleKeys largeComplementCount
        + cube contribution.

This avoids replacing variable multiplicity by a crude constant.

## Phase 14 — Cross isolation theorem

Rearrange only after proving the additive conservation law.

Preferred Nat-safe statement:

    Cross + RoutedCompositeMass = TotalAboveNQuotients.

Then obtain:

    Cross <= TotalAboveNQuotients,

and, more importantly, any structural lower bound on routed composite mass yields a sharper Cross upper bound.

Do not expose `Total - Routed` as the primary theorem unless the required inequality for Nat subtraction is already proved.

## Phase 15 — candidate structural gain from repeated/triple mass

Use the exact Repeated/Triple key counts already available.

Test whether their routed complementary quotients account for a meaningful portion of `TotalAboveNQuotients` on calibration anchors.

Mandatory anchors:

    211,503,1009,1013,1019,1021.

For each report:

    Cross,
    TotalAboveNQuotients,
    routed Cube mass,
    routed Repeated mass,
    routed Triple mass,
    residual.

The residual must equal Cross by theorem if conservation is complete.

## Phase 16 — bounded diagnostics beyond calibration

Run a bounded prime-anchor scan over a justified finite range.

Record:

- ratio Cross / TotalAboveNQuotients;
- share removed by Repeated routing;
- share removed by Triple routing;
- largest owner-p residual fiber;
- whether routed composite mass grows enough to materially improve the old summed floor capacity.

Preserve full output.

Do not infer asymptotics.

## Phase 17 — range decomposition of owners p

If exact quotient conservation still leaves a coarse total capacity, partition owner p by finite geometric ranges.

Suggested starting ranges:

    sqrt n < p <= 2 sqrt n,
    2 sqrt n < p <= 3 sqrt n,
    ...

or dyadic-like integer ranges if easier in Nat.

For each range derive exact or safe quotient-window length/carry bounds.

Keep the number of ranges finite and explicitly dependent on n only if necessary.

Do not introduce real-valued asymptotics.

## Phase 18 — primality-aware capacity without analytic estimates

Only after exact routing is complete, investigate additional elementary restrictions on CrossFiber:

- q is odd prime;
- q>n;
- q lies in a short quotient interval;
- q is coprime to 2n automatically;
- distinct q values have parity spacing at least2.

Prove every finite combinatorial improvement available from these facts.

Do not invoke PNT, Bertrand, Brun, Selberg, Mertens, RH, or analytic sieve estimates.

## Phase 19 — compare against final census demand

Insert the best Cross upper bound into

    Cube + Cross + Repeated + Triple < R.

Use `Cube<=1` exactly where helpful.

Determine whether the new routed bound proves new prime anchors structurally beyond the existing calibration set.

If yes, add at least one new kernel-checked endpoint.

If not, quantify the smallest deficit at representative hard anchors.

## Phase 20 — identify the next irreducible arithmetic obstruction

At the end, answer:

> After composite quotient routing, what remains genuinely dependent on the primality of external q?

Possible outcomes:

- Cross is sharply isolated and only a prime-in-short-interval bound remains;
- composite routing already supplies enough cancellation for a uniform inequality;
- owner quotient total is still too coarse and needs a stronger lower bound on routed mass;
- a new arithmetic type appears.

State one exact theorem contract for the next step.

## Possible outcomes

### Outcome A — quotient conservation sharply isolates Cross

An exact global quotient conservation law is proved, composite quotient mass is routed into the existing factorization census with correct owner multiplicity, and Cross receives a strictly sharper structural upper bound than the old summed quotient capacity.

### Outcome B — exact routing complete, quantitative gain limited

The prime/composite partition and global routing law are complete, but the resulting Cross bound is still too coarse to improve the uniform frontier materially.

### Outcome P — one precise owner-multiplicity bridge remains

Pointwise quotient routing is proved, but exact global summation is blocked by a specific repeated/triple owner-multiplicity theorem.

### Outcome C — composite quotient routing is not compatible with the proposed conservation

A genuine additional quotient class or noncanonical owner ambiguity prevents the intended law. Preserve the smallest counterexample and state the corrected decomposition.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    PNT/RH;
    Bertrand;
    Brun/Selberg sieve;
    analytic prime-counting estimates;
    FLT/ABC consequences.

Do not evaluate whole E or whole I as a structural proof.

Do not replace exact CrossFiber with all integers in its geometric interval.

Do not identify external q>n with active secondary labels q<=n.

Do not create duplicate census or support universes.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

A focused module split is reasonable, for example:

    DkMath/NumberTheory/Legendre/ParitySafeSqrtCrossQuotient.lean
    DkMath/NumberTheory/Legendre/ParitySafeSqrtCompositeRouting.lean
    DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean.

Extend `ParitySafeSqrtRoughSingleton` only for quotient/fiber lemmas that naturally belong there.

Reuse the existing product-key bijections from the census instead of re-factorizing seats.

Keep neutral finite partition/cardinality lemmas outside the Legendre namespace when useful.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for every new public declaration;
- git diff --check.

All new production declarations must remain free of sorryAx.

Keep the existing project convention for file headers and import-adjacent

    #print "file: ..."

markers on every modified/new Lean file.

## Durable checkpoint protocol

Update findings after:

- exact quotient carrier;
- CrossFiber prime filter;
- prime/composite partition;
- quotient-to-seat packet;
- composite normal forms;
- repeated/triple owner multiplicity;
- above-n multiplicity refinement;
- global quotient conservation;
- Cross isolation;
- calibration table;
- bounded diagnostic scan;
- final A/B/P/C judgment.

Preserve false owner-multiplicity conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact owner-p quotient carrier was used?
2. Is CrossFiber exactly its prime-above-n part?
3. What complementary quotient classes occur?
4. How does each Cube/Repeated/Triple seat route into owner quotient fibers?
5. What exact owner multiplicity does each factorization type have?
6. What changes when only q>n quotients are retained?
7. What exact global quotient conservation identity was proved?
8. What sharper Cross upper bound follows?
9. Does the routed bound prove any new prime anchors or materially reduce the deficit?
10. What external-prime arithmetic theorem remains after routing?

End with exactly one judgment:

    Outcome A — QUOTIENT CONSERVATION SHARPLY ISOLATES CROSS
    Outcome B — EXACT ROUTING COMPLETE, QUANTITATIVE GAIN LIMITED
    Outcome P — PRECISE OWNER-MULTIPLICITY BRIDGE REMAINS
    Outcome C — COMPOSITE ROUTING REQUIRES A CORRECTED DECOMPOSITION