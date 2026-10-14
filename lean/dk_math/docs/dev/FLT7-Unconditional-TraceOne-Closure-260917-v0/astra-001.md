# FLT7 Astra Integrated Search Brief — R17 handoff

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Use the current repository HEAD as authoritative. Read ROADMAP.md and reports
013 through 022 before drawing conclusions. In particular, report-022.md is
the current frontier.

## Mission

Find the shortest noncircular, receiver-free route from the current direct
FLT7 provenance to either:

1. a kernel-checkable contradiction, or
2. a genuine strict descent with an explicitly well-founded measure.

Do not prioritize writing Lean code. Prioritize mathematical synthesis:
identify the decisive invariant, prove or disprove the route conceptually, and
reduce the result to the smallest implementable theorem chain.

The target surface is:

    PrimitiveCounterexampleRamifiedProvenance source -> False

or a stronger provenance-preserving impossibility theorem implying it.

## Hard constraints

Do not use as assumptions:

- CubicGapSeventhShapeReceiver;
- RamifiedSignedRootRoutingPacket;
- any theorem whose decisive dependency includes sorryAx;
- any historical reconstruction packet unless its hypotheses are proved from
  the current direct provenance without circularity.

Do not:

- identify elements merely because their norms agree;
- drop associated units without a checked theorem;
- promote local congruences to global descent without a bridge;
- call a real-cubic seventh-power equation an integer FLT7 solution;
- call something a descent without constructing both the smaller state and a
  strict well-founded measure.

## Verified direct route

For a primitive positive natural FLT7 counterexample, current provenance gives
a ramified summit with oriented integers L,R and positive natural roots A,B
such that conceptually:

    L - R = 7^6 * A^7
    cyclotomicSeven L R = 7 * B^7
    distinguished = 7 * A * B
    gcd(A,B) = 1

and the oriented endpoints and their sum are seven-units.

Let zeta be the concrete primitive seventh root in the degree-six cyclotomic
integer carrier and let pi = 1-zeta.

The current direct route proves unconditionally:

    L - zeta*R = pi * gamma^7

for an integral cyclotomic gamma.

The concrete carrier has been proved equivalent to the full ring of integers
of Q(zeta_7). The associated Kummer unit was removed by explicit CM
conjugation, torsion-order 14, and a full-(7) phase-kill theorem.

The root gamma can be normalized uniquely up to the mu_7 gauge at first
ramified order. For the normalized root gammaNorm:

    gammaNorm^7 = Q1
    Norm_{Q(zeta_7)/Q}(gammaNorm) = B

and

    gammaNorm - c in ramifiedPrime^2

for a canonical integer residue lift c.

The seventh-power gain and rational contraction give:

    endpointRight ≡ c^7 (mod 49).

R17 proves that, for units modulo 49, being a seventh power is equivalent to
u^6=1. Therefore this local endpoint gate is exhausted: it adds no branch
reduction beyond the pre-existing endpoint sixth-root condition.

Do not spend search budget trying to extract a contradiction from this same
mod-49 gate alone.

## Verified real-cubic transition

Let K+ be the maximal real cubic subfield and theta = eisensteinAxis.

For the R16 normalized cyclotomic root define

    rho = Norm_{K/K+}(gammaNorm).

R17 proves exactly:

    directChosenQuotientRealSource = rho^7
    Norm_{K+/Q}(rho) = B
    theta does not divide rho
    thetaResidue rho != 0.

The source has the explicit form

    S0 = L*R - theta^35 * U^12 * A^14

where U = thetaSevenUnit and

    7 = theta^3 * U.

Let sigma = SevenRealCubicInt.rotateEquiv, of order 3.

Define:

    rho0 = rho
    rho1 = sigma(rho)
    rho2 = sigma^2(rho)

and similarly S0,S1,S2. R17 proves:

    S0 = rho0^7
    S1 = rho1^7
    S2 = rho2^7.

The first orbit edge is now kernel-checked exactly as:

    S1 - S0
      = orbitUnit01 *
        (theta^5 * U * A^2)^7.

Here orbitUnit01 is explicit, source-independent, and a global unit:

    orbitUnit01
      = (pairAxisUnit 1 - 1) * alphaAddOneInv * U^5.

Its projective unit class is exactly:

    projectiveLog orbitUnit01Unit = (0,5) in (Z/7)^2.

Therefore:

    orbitUnit01 is NOT a seventh power unit.

This is a verified global unit-class obstruction, but not yet a contradiction.

Axiom audits for the decisive R17 chain use only:

    propext
    Classical.choice
    Quot.sound

No sorry/sorryAx/admit/unsafe/project axiom is allowed in the proposed route.

## Current precise frontier

No clean current-provenance theorem presently controls both:

    rho1 - rho0

and the homogeneous quotient

    H7(rho1,rho0)
      = (rho1^7-rho0^7)/(rho1-rho0)

at the theta-adic and prime-support levels.

The currently identified missing bridge is:

1. theta-adic factorization/depth of rho1-rho0;
2. prime-support/coprimality control between rho1-rho0 and H7(rho1,rho0);
3. compatibility of that split with the verified equation
   orbitUnit01 * W^7.

Historical theta-coordinate, coprime-extraction and AxisDrop machinery exists,
but does not currently consume this direct provenance.

## Highest-priority Astra search: the full three-edge orbit

Do NOT analyze only the 0->1 edge.

Construct or conceptually determine the corresponding equations:

    rho1^7-rho0^7 = epsilon01 * W01^7
    rho2^7-rho1^7 = epsilon12 * W12^7
    rho0^7-rho2^7 = epsilon20 * W20^7

with epsilon_ij units.

Determine the exact Galois action on projective unit classes:

    projectiveLog(sigma(u))

as a linear or affine action on (Z/7)^2, if possible.

The repository does not yet expose this action explicitly.

Investigate:

- the three classes [epsilon01], [epsilon12], [epsilon20];
- whether they are Galois transforms of (0,5);
- their sum/product/cocycle relation;
- whether sigma^3=1 forces a class relation incompatible with all three edge
  equations;
- whether the telescoping identity
      (rho1^7-rho0^7)+(rho2^7-rho1^7)+(rho0^7-rho2^7)=0
  creates a nontrivial constraint after unit-class normalization;
- whether the product of the three edge equations, combined with
      rho0*rho1*rho2 = B
  or the exact real-cubic norm identity, forces a seventh-power unit class
  contradiction.

A contradiction must be explicitly derived; the nonzero class of one edge
alone is not enough.

## Theta-adic / prime-support search

For the first edge write:

    rho1^7-rho0^7
      = (rho1-rho0) * Phi7(rho1,rho0)
      = orbitUnit01 * W^7.

Determine the exact theta valuations of both factors.

Questions:

1. Does theta divide rho1-rho0?
2. What is the exact v_theta(rho1-rho0)?
3. What is the exact v_theta(Phi7(rho1,rho0))?
4. Outside theta, are the two factors coprime?
5. Can a common non-theta prime be excluded from:
       rho1-rho0
       and
       Phi7(rho1,rho0)
   using rho being theta-unit, gcd(A,B)=1, Galois symmetry, or the exact norm?
6. If the two factors are coprime away from theta, how must the fixed unit
   class (0,5) distribute across the factors?
7. Does that distribution force one factor to have an impossible unit class?

Search the existing generic Kummer lemmas before inventing new ideal theory.

## Exact-norm constraints

Use all of:

    Norm(rho0) = Norm(rho1) = Norm(rho2) = B
    gcd(A,B)=1
    theta ∤ rho_i.

Investigate whether these imply:

- pairwise coprimality or controlled gcd of the rho_i;
- controlled gcd of rho_i-rho_j with B;
- a norm formula for rho1-rho0 whose prime support is incompatible with A;
- a descent in B or A.

Do not assume these; derive them.

## Historical machinery to mine, not to assume

Audit and extract generic statements from:

- SevenRealCubicThetaCoordinates
- SevenRealCubicThetaSeventhPower
- SevenRealCubicCoprimeExtraction
- SevenRealCubicAxisDrop
- SevenRealCubicUnitClass
- SevenRamifiedFusionRotationPhase
- SevenRamifiedFusionRealPairCarrier
- SevenRamifiedFusionRealPairCoprimalityNormGate

The goal is to identify which historical lemmas can be generalized so that
their inputs are only current direct data.

Do not instantiate a historical packet merely because the formulas resemble
the new orbit.

## Strict-descent search

If the orbit split can produce a new state, specify it exactly.

Possible measures to investigate include:

    |B|
    |A|
    |Norm(rho1-rho0)|
    theta-adic depth paired with an Archimedean height
    a primitive height derived from the integer endpoints.

A valid descent proposal must include:

1. construction of the successor arithmetic state;
2. proof it satisfies the same required primitive hypotheses;
3. an explicit strict inequality in a well-founded order.

If any of these is missing, classify the route as not yet a descent.

## Generalization extraction

If visible, formulate a receiver-free p-th-prime principle behind this route:

    cyclotomic phase support localization
    -> ramified load removal
    -> CM unit-phase kill
    -> exact p-th power in K
    -> relative norm to K+
    -> Galois orbit edge = fixed unit class * p-th power
    -> orbit compatibility / local-global intersection obstruction.

Call this a candidate Gauge Intersection / Galois Orbit Obstruction Principle
only if the precise algebraic hypotheses can be stated.

FLT7 closure remains the priority; do not spend most of the search budget on
generalization.

## Required deliverable

Return a report with exactly these sections.

### A. New verified deductions

Only deductions that follow from repository facts plus explicit mathematical
arguments. Separate any conjectural step.

### B. Full three-edge unit-class analysis

Give the unit-class action of sigma if derivable, all three edge classes, and
their compatibility relations.

### C. Theta-adic factorization analysis

Give the strongest proved/derivable statements about:

    rho1-rho0
    Phi7(rho1,rho0)

including exact or candidate valuations and gcd support.

### D. Candidate closure routes

At most three routes. For each give:

- exact theorem chain;
- first missing theorem;
- whether it leads to contradiction or strict descent;
- why it is noncircular.

### E. Rejected routes

Explicitly identify information-equivalent local gates, circular receiver
routes, or mathematically nonproductive branches.

### F. Best next bounded checkpoint

Give ONE implementation checkpoint for Codex/LUNA, with suggested theorem
shapes and hard stops.

### G. Confidence

Classify:

- A: direct implementation likely closes primitive FLT7;
- B: strong route with one substantial bridge;
- C: structural progress but closure mechanism not yet visible;
- D: this orbit route appears nonproductive.

Do not claim unconditional FLT7 unless the complete noncircular theorem chain
has been exhibited.
