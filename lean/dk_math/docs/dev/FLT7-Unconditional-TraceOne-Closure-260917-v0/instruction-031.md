# FLT7TC-005R25 — Weighted-gap nondivisibility and ordinary self-similarity closeout

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-030.md
- PrimeTraceOneDirectRealCubicLocalClass.lean
- PrimeTraceOneDirectRealCubicTwistClass.lean
- PrimeTraceOneDirectRealCubicSuccessorAudit.lean
- SevenRamifiedFusionRealPairCarrier.lean
- SevenRamifiedFusionRotationPhase.lean

R24 productionized the universal local classes:

    quotientUnit = (5,1)
    gapUnit      = (2,4)

and hence the successor coefficient classes/ratio classes.

This checkpoint decides whether the ordinary homogeneous seventh-power
difference factorization can restart on the smaller twisted state.

The expected answer is negative, and should be proved directly by theta
residues rather than by projectiveLog alone.

## Part A — scalar residue of the transport unit P

Let:

    P := directOrbitPairAxisUnitOne.

Reuse:

    pairAxisUnit_thetaResidue_eq_pairPhase
    pairPhase_one_val

to prove:

    thetaResidue (P : SevenRealCubicInt) = 4.

Do not unfold the full cubic coordinates if the existing pair-phase theorem is
available.

## Part B — exponent reduction in the residue-field unit group

For:

    e := 32 + 42*k

prove the residue-field power identity:

    (4 : ZMod 7)^e = 2.

Preferred route:

    e = 2 mod 6

and Fermat/unit-group periodicity, or simply a kernel-checked arithmetic
rewriting of 42*k and 32.

Do not confuse this with the already proved projective-log reduction
e = 4 in ZMod 7. These are different exponent reductions:

- projective additive class uses mod 7;
- multiplicative nonzero residue uses mod 6.

Expose this distinction in the comments/report.

## Part C — coefficient-ratio scalar residues

For every current DirectOrbitPowerSplitPacket s, prove:

    thetaResidue
      ((directOrbitTwistedCoeff1 s *
        (directOrbitTwistedCoeff0 s)⁻¹ : SevenRealCubicInt)) = 2.

Use:

- coeff1 = P^e * rotateUnit(coeff0);
- thetaResidue_rotateEquiv;
- thetaResidue of a unit inverse;
- cancellation of thetaResidue coeff0;
- Part A/B.

Do not use the projectiveLog ratio class to infer the scalar residue.

Optionally compute the other two cyclic coefficient-ratio scalar residues as
well if they are cheap and useful.

## Part D — coefficient difference is a theta-unit

From Part C prove:

    thetaResidue
      ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
       (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) != 0.

Equivalently:

    ¬ eisensteinAxis ∣
      ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
       (directOrbitTwistedCoeff0 s : SevenRealCubicInt)).

A convenient proof is to factor:

    eps1 - eps0 = eps0 * ((eps1*eps0^-1) - 1)

and use ratio residue 2, hence ratio-1 residue 1.

Do not rely on projectiveLog nonzero; the scalar residue theorem is stronger
for this divisibility question.

## Part E — successor root gap is theta-divisible

For the transported twisted state/current packet prove:

    eisensteinAxis ∣
      rotateEquiv s.gapRoot - s.gapRoot.

This should follow immediately from:

    thetaResidue_rotateEquiv

and the axis-divisibility iff theta-residue-zero theorem.

Also retain:

    ¬ eisensteinAxis ∣ s.gapRoot

from R23.

Hence:

    ¬ eisensteinAxis ∣ s.gapRoot^7.

## Part F — weighted remainder is not theta-divisible

Define conceptually:

    rem :=
      ((eps1 : O) - (eps0 : O)) * s.gapRoot^7.

Using Parts D/E prove:

    ¬ eisensteinAxis ∣ rem.

Prefer prime-divisibility/unit-residue reasoning rather than coordinate
expansion.

## Part G — ordinary root-gap divisibility fails

Use the existing exact identity:

    eps1 * root1^7 - eps0 * root^7
      =
    eps1 * (root1^7 - root^7)
      + (eps1-eps0) * root^7.

The first summand is divisible by:

    root1 - root

via the ordinary difference-of-seventh-powers factorization.

Assume for contradiction that the full weighted difference is divisible by:

    root1 - root.

Then the remainder is divisible by root1-root.

But:

    theta ∣ root1-root,

so theta would divide the remainder, contradicting Part F.

Prove the decisive theorem, conceptually:

    theorem directOrbit_weighted_difference_not_gap_dvd
      (s : DirectOrbitPowerSplitPacket p) :
      ¬ (rotateEquiv s.gapRoot - s.gapRoot) ∣
        ((eps1 : O) * (rotateEquiv s.gapRoot)^7 -
         (eps0 : O) * s.gapRoot^7)

with the exact repository orientation.

This theorem is the main checkpoint result.

## Part H — no ordinary homogeneous quotient restart

Record an explicit corollary/audit theorem:

There is no q : SevenRealCubicInt such that

    eps1 * root1^7 - eps0 * root^7
      =
    (root1-root) * q.

Therefore the existing neutral HomogeneousPowerQuotient machinery cannot be
reapplied to the R22/R23 successor state using the ordinary root gap.

This is a negative structural theorem, not a contradiction of the state.

## Part I — optional no unit-gauge linear normalization

Because R24 also proves that eps1/eps0 is not a seventh power unit, optionally
prove:

There is no unit v with:

    eps1 = eps0 * v^7.

Thus no unit rescaling:

    root1' := v * root1

can turn the weighted pair into a common-coefficient ordinary seventh-power
difference.

If the theorem already exists unconditionally after R24, simply expose/reuse
it.

Do not attempt fraction-field seventh-root extensions in this checkpoint.

## Part J — route decision

Update ROADMAP/report with a clear conclusion.

If Parts A-H are green:

    The smaller twisted state is NOT self-similar under the ordinary
    homogeneous-gap extraction mechanism.

At that point freeze the naive iterable twisted-descent route.

The next research choices are only:

1. construct a genuinely weighted/twisted factorization kernel adapted to
   u*x^7-v*y^7, without assuming a seventh root of v/u; or
2. return to a different successor notion/hybrid reconstruction.

Do not automatically choose route 1. First record the negative theorem.

## Hard stops

- Do not infer scalar theta residue from projectiveLog alone.
- Do not claim the weighted difference factors by root1-root.
- Do not adjoin a seventh root of a unit ratio silently.
- Do not call failure of self-similarity a contradiction of FLT7.
- No historical receiver/routing packet.
- No successor recursion/descent theorem.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionAxiom.lean

Create report-031.md and update ROADMAP.md.

## Report questions

1. Was thetaResidue(P)=4 proved from the existing pair-phase API?
2. Was 4^(32+42*k)=2 in ZMod 7 proved?
3. Was the first successor coefficient-ratio residue proved equal to 2?
4. Was eps1-eps0 proved theta-nondivisible?
5. Was rotate(g)-g proved theta-divisible?
6. Was the weighted remainder proved theta-nondivisible?
7. Was the weighted difference proved NOT divisible by rotate(g)-g?
8. Was ordinary homogeneous-quotient restart formally ruled out?
9. Was unit-gauge normalization also ruled out?
10. Should the naive twisted self-similarity route now be frozen?

## Outcomes

- Outcome A — WEIGHTED GAP NONDIVISIBILITY GREEN; ORDINARY SELF-SIMILARITY
  FORMALLY RULED OUT.
- Outcome B — COEFFICIENT-DIFFERENCE THETA-UNIT GREEN; FINAL GAP-DIVISIBILITY
  CONTRADICTION NEEDS A SMALL BRIDGE.
- Outcome C — COEFFICIENT-RATIO SCALAR RESIDUE GREEN; DIFFERENCE DEPTH IS THE
  PRECISE FRONTIER.
- Outcome D — EXPECTED RESIDUE OBSTRUCTION FAILS; REOPEN THE SUCCESSOR AUDIT.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicWeightedGapObstruction
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicWeightedGapObstructionAxiom
    git diff --check

Print axioms for:

- pair-axis scalar residue;
- coefficient-ratio scalar residue;
- coefficient-difference theta-nondivisibility;
- successor root-gap theta-divisibility;
- weighted remainder theta-nondivisibility;
- weighted difference nondivisibility theorem;
- ordinary quotient restart obstruction.

Run forbidden-source/import scans on every decisive file.
