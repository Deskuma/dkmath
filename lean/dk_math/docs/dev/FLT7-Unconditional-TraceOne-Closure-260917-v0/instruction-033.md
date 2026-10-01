# FLT7TC-005R27 — Square-refined twisted signature audit

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-028.md
- report-031.md
- report-032.md
- PrimeTraceOneDirectRealCubicSuccessorAudit.lean
- PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean
- PrimeTraceOneDirectRealCubicSquareRefinement.lean
- PrimeTraceOneDirectRealCubicOrbitGapHeight.lean
- SevenRealCubicEisenstein.lean

R25 rules out ordinary seventh-power self-similarity.
R26 proves a new square refinement:

    gapRoot = gapSquareUnit * gapSquareRoot^2.

This checkpoint asks one bounded question:

Does the square refinement turn the twisted successor equation into an
impossible sum of three squares, or does it expose a second unit obstruction?

Do not build a full unit-group-mod-squares classification unless the concrete
current equation first proves it is necessary.

## Part A — square-refined twisted equation

Let t : DirectOrbitSquareRefinementPacket p.

Write:

    s  := t.powerSplit
    r0 := t.gapSquareRoot
    r1 := rotateEquiv r0
    r2 := rotateEquiv r1

    u0 := t.gapSquareUnit
    u1 := directOrbitRotateUnit u0
    u2 := directOrbitRotateUnit u1

and let eps0, eps1, eps2 be the R22/R23 twisted coefficients.

Define new coefficient units:

    c0 := eps0 * u0^7
    c1 := eps1 * u1^7
    c2 := eps2 * u2^7.

Use:

    s.gapRoot = u0 * r0^2

and its two rotations to rewrite the existing twisted seventh-power equation
as the exact square-weighted equation

    (c0 : O) * (r0^7)^2 +
    (c1 : O) * (r1^7)^2 +
    (c2 : O) * (r2^7)^2 = 0.

No unit may be dropped.

Expose this as a stable production theorem.

## Part B — coefficient transport survives square refinement

Prove:

    c1 = P^e * rotateUnit c0
    c2 = P^e * rotateUnit c1

where

    P := directOrbitPairAxisUnitOne
    e := 32 + 42*s.gapSplit.k.

This should follow because rotation commutes with the seventh power of u0.

Also prove:

    Even e.

Hence construct a unit peHalf with:

    P^e = peHalf^2.

The literal choice

    peHalf := P^(e/2)

is preferred, with a checked exponent identity.

## Part C — projective classes remain unchanged modulo seventh powers

Since each ui^7 has zero projectiveLog, prove:

    projectiveLog c0 = projectiveLog eps0 = (2,4)
    projectiveLog c1 = projectiveLog eps1 = (2,2)
    projectiveLog c2 = projectiveLog eps2 = (2,5).

Likewise, if useful, show the ratio projective classes remain:

    (0,5), (0,3), (0,6).

This is bookkeeping only. It does NOT decide square classes.

## Part D — nonzero square variables

From the R26 theorem:

    0 < natAbs (norm r0)

prove:

    r0 != 0
    r1 != 0
    r2 != 0.

Under the existing chosen real embedding realEval, prove:

    realEval (r0^7) != 0
    realEval (r1^7) != 0
    realEval (r2^7) != 0.

Use injectivity of realEval, not numerical approximation.

## Part E — conditional square-unit contradiction

Prove a theorem of the following shape:

If

    ∃ v0 : Oˣ, c0 = v0^2,

then False.

Reason:

1. From Part B and Even e, c1 is also a square unit:
       c1 = (peHalf * rotateUnit v0)^2.
2. Rotate once more to make c2 a square unit.
3. Apply realEval to the square-weighted equation.
4. Every coefficient evaluates to a strictly positive real number because a
   nonzero real square is positive.
5. Every variable square (realEval (ri^7))^2 is strictly positive.
6. The sum of three strictly positive reals cannot be zero.

Do not use “totally real” as an informal slogan; prove positivity through the
actual realEval and rotation equations.

Conclude unconditionally:

    ¬ ∃ v0 : Oˣ, c0 = v0^2.

This is a structural consequence of the assumed current counterexample
provenance, not an FLT7 contradiction.

## Part F — signed norm of the first square coefficient

Prove:

    norm c0 = 1.

A preferred route is:

- directOrbitGap has positive norm from R21;
- directOrbitGap = theta^e * gapCore;
- e is even and norm(theta) = -7, hence norm(theta^e) > 0;
- gapCore = c0 * r0^14;
- norm(r0^14) > 0;
- norm(c0) is a unit in Z, hence ±1.

Therefore its sign must be +1.

Do not infer norm(c0)=1 merely from c0 being a unit.

## Part G — cyclic sign obstruction

Using:

    realEval_cyclic_norm c0

and norm c0 = 1, prove that the three real conjugate values

    realEval c0
    realEval (rotateEquiv c0)
    realEval (rotateEquiv (rotateEquiv c0))

have positive product.

Then prove they cannot all be positive:
if they were all positive, Part B implies c1,c2 have positive realEval
coefficients and the square-weighted equation contradicts positivity.

They also cannot all be negative because their product is positive.

Record the strongest clean finite conclusion convenient in Lean, e.g.:

    at least one conjugate value is positive
    and at least one conjugate value is negative.

If a clean exact statement “exactly two negative, one positive” is easy,
prove it; otherwise do not block on packaging.

This is the current coefficient-sign obstruction.

## Part H — square-gauge normalization closeout

Prove the concrete no-normalization corollary:

There is no unit v such that

    c0 = v^2.

If desired, also show there do not exist square-unit rescalings of all three
variables that turn the current equation into

    X0^2 + X1^2 + X2^2 = 0.

This should be a corollary of Part E.

Do NOT introduce a global UnitClassModTwo API merely for this theorem.

## Part I — audit whether any existing theorem contradicts the forced sign class

Read-only audit after Parts E-G.

Search the current checked repository for a theorem forcing c0 or its defining
factors to be:

- a square unit;
- totally positive;
- or of a fixed incompatible real signature.

In particular inspect only current direct-route facts about:

    gapUnit
    gapSquareUnit
    orbit/successor transport units.

Do not import historical receiver/routing assumptions.

If such a theorem exists, instantiate it and close the contradiction.
If not, explicitly record:

    the square refinement does not close FLT7;
    it forces a non-square mixed-sign coefficient unit.

## Part J — route decision

If no contradiction is found, freeze the repeated power-refinement route:

- seventh-power gauge normalization is obstructed (R24/R25);
- ordinary homogeneous restart is obstructed (R25);
- square-gauge normalization is obstructed (this checkpoint).

The remaining serious choices are then:

1. a genuinely new weighted/unit-sign arithmetic invariant;
2. a different hybrid successor reconstruction;
3. a fresh integrated research pass using all R21-R27 facts.

Do not automatically continue extracting more powers.

## Hard stops

- No assumption that every norm-one unit is a square.
- No inference of square class from projectiveLog mod 7.
- No floating-point sign calculations.
- No historical receiver/routing packet.
- No claim of FLT7 contradiction unless an independent checked theorem forces
  c0 to be square/totally positive.
- No successor recursion or infinite descent claim.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionAxiom.lean

Create report-033.md and update ROADMAP.md.

## Report questions

1. Was the exact unit-weighted three-square equation proved?
2. Was coefficient transport c1=P^e*sigma(c0), c2=P^e*sigma(c1) proved?
3. Was e proved even and P^e exposed as a square unit?
4. Were all square variables proved nonzero?
5. Was “c0 square unit -> False” kernel-checked?
6. Was norm(c0)=1 proved?
7. Was mixed real signature of c0 proved?
8. Was square-gauge normalization formally ruled out?
9. Does any existing current-route theorem force c0 to be square or totally
   positive?
10. Should repeated power-refinement now be frozen?

## Outcomes

- Outcome A — CURRENT DIRECT DATA FORCES c0 SQUARE/TOTALLY POSITIVE; FLT7
  CONTRADICTION GREEN.
- Outcome B — SQUARE-WEIGHTED STATE GREEN; c0 PROVED NON-SQUARE WITH MIXED REAL
  SIGNATURE; POWER-REFINEMENT ROUTE FROZEN.
- Outcome C — SQUARE-WEIGHTED EQUATION GREEN; REAL-SIGN BRIDGE IS THE PRECISE
  FRONTIER.
- Outcome D — SQUARE SUBSTITUTION DOES NOT PRODUCE THE EXPECTED TRANSPORTED
  STATE; REOPEN R26 INTERPRETATION.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareTwistObstructionAxiom
    git diff --check

Print axioms for:

- square-weighted twisted equation;
- coefficient transport;
- even transport exponent / square transport factor;
- c0-not-square theorem;
- norm(c0)=1;
- mixed-sign theorem;
- square-gauge normalization obstruction.

Run forbidden-source/import scans on every decisive file.
