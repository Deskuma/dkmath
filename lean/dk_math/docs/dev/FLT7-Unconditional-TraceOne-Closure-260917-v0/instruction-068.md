# FLT7TC-005R62 — Current phase-corrected degree-six linear carrier

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-067.md when available
- SevenRealCubicCurrentResidueKernel.lean
- SevenRealCubicCurrentOrientationRatio.lean
- SevenRealCubicCurrentKummerPhaseSieve.lean
- SevenRealCubicCurrentCommonPrimePacket.lean
- SevenRealCubicCurrentCyclotomicAddress.lean
- SevenRealCubicCurrentCyclotomicPhase.lean
- SevenRealCubicCurrentQuotientGapOrientation.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
- SevenRamifiedFusionCyclotomicAdditiveChartBoundary.lean
- SevenRamifiedFusionRealPairCarrier.lean
- SevenRamifiedFusionOrientedCarrierValuationOwnership.lean

Strategic position:

R61 production now gives:

- same-kernel ZMod evaluation uniqueness;
- quotient/gap orientation as tau = delta or delta^-1;
- phase/inversion blindness of the real Kummer condition;
- a finite Kummer sieve;
- every current common prime q >= 379;
- c >= 379 and 379*u^5 < v.

The next new information must be genuinely degree-six and orientation-sensitive.

R62 constructs, from the CURRENT quotient-side phase data, an explicit linear
cyclotomic factor whose selected current degree-six kernel contains it while
the conjugate kernel excludes it.

This is the current-provenance analogue of the historical FUSION oriented
linear carrier. Do not import historical terminal packets.

## Part A — phase inverse exponent

For

    c : CurrentCommonPrimeCyclotomicPacket h q

let

    m := c.phase.val + 1

so m is one of 1,2,3 and

    c.ratio = c.tau^m.

Define the inverse exponent modulo seven:

    phaseInverseExponent 0 = 1
    phaseInverseExponent 1 = 4
    phaseInverseExponent 2 = 5.

Prove by Fin-3 case split:

    m * phaseInverseExponent c.phase ≡ 1 [MOD 7].

Also prove the exact unit-power identity

    c.ratio ^ phaseInverseExponent c.phase = c.tau.

Use c.tau_pow_seven. Do not use a generic modular-exponent framework if a
finite proof is shorter.

## Part B — phase-corrected seventh root in the degree-six carrier

Define

    currentPhaseZeta c :=
      SevenCyclotomicDegreeSixInt.zeta ^
        phaseInverseExponent c.phase.

Prove under the current local evaluation:

    c.address.currentLocalEval (currentPhaseZeta c) =
      (c.tau : ZMod q).

Under the conjugate local evaluation prove:

    c.address.conjugate.currentLocalEval (currentPhaseZeta c) =
      ((c.tau^-1 : (ZMod q)^x) : ZMod q).

Also prove:

- currentPhaseZeta^7 = 1;
- currentPhaseZeta != 1;
- star currentPhaseZeta = currentPhaseZeta^-1.

The exact nontriviality proof may use the three explicit exponents.

## Part C — phase-corrected current linear carrier

Let

    rho0 := p.rho
    rho1 := rotateEquiv p.rho.

Define

    currentLinearCarrier c :=
      ofReal rho1 -
        currentPhaseZeta c * ofReal rho0.

Define its quadratic conjugate either by star or explicitly:

    currentConjugateLinearCarrier c :=
      star (currentLinearCarrier c).

Prove the explicit formula

    currentConjugateLinearCarrier c =
      ofReal rho1 -
        (currentPhaseZeta c)^-1 * ofReal rho0.

## Part D — oriented local ownership

Prove:

    c.address.currentLocalEval (currentLinearCarrier c) = 0.

This should reduce to the definition of tau:

    evalReal rho1 = tau * evalReal rho0.

Then prove:

    c.address.conjugate.currentLocalEval
      (currentLinearCarrier c) != 0.

Use:

- evalReal rho0 != 0;
- tau != tau^-1, since orderOf tau = 7.

Likewise prove the conjugate statements:

    conjugate current carrier vanishes at conjugate.currentKernel;
    conjugate current carrier is nonzero at currentKernel.

Expose the ideal-membership packet:

    currentLinearCarrier c ∈ c.address.currentKernel
    currentLinearCarrier c ∉ c.address.conjugate.currentKernel
    currentConjugateLinearCarrier c ∈ c.address.conjugate.currentKernel
    currentConjugateLinearCarrier c ∉ c.address.currentKernel.

This is the mandatory orientation-sensitive endpoint.

## Part E — neutral current real-pair factors

Do not depend on RamifiedSignedRootDepthPacket.realPairCarrier.

Define a neutral three-phase real carrier for arbitrary x y:

    currentRealPairCarrier (i : Fin 3) (x y : SevenRealCubicInt) :=
      x^2 -
        (currentCyclicAlpha i - 1) * x * y +
        y^2

where currentCyclicAlpha is the neutral explicit triple

    i=0 : alpha
    i=1 : alpha^2 - 2*alpha
    i=2 : -alpha^2 + alpha + 2.

If practical, refactor the existing historical cyclicAlpha formula into a
neutral namespace rather than duplicate it. Do not force a broad refactor.

Prove the neutral factorization:

    currentRealPairCarrier 0 x y *
    currentRealPairCarrier 1 x y *
    currentRealPairCarrier 2 x y
      = seventhQuotient x y.

This should be an algebraic proof from alpha_cube.

## Part F — phase trace index

Define the phase-selected real-pair index:

    phaseTraceIndex 0 = 0
    phaseTraceIndex 1 = 2
    phaseTraceIndex 2 = 1.

This is the index whose real trace corresponds to tau + tau^-1 after the
phase correction.

Prove exactly:

    currentPhaseZeta c +
      (currentPhaseZeta c)^-1
      =
    ofReal (currentCyclicAlpha (phaseTraceIndex c.phase) - 1).

A Fin-3 proof using the explicit zeta relation is acceptable.

Then define

    selectedRealPairCarrier c :=
      currentRealPairCarrier
        (phaseTraceIndex c.phase)
        (rotateEquiv p.rho)
        p.rho.

## Part G — quadratic norm/product identity

Prove:

    currentLinearCarrier c *
      currentConjugateLinearCarrier c
      =
    ofReal (selectedRealPairCarrier c).

Equivalently prove the QuadraticAlgebra norm identity.

Then prove:

    c.residue.evalReal (selectedRealPairCarrier c) = 0.

Prefer deriving this from the current linear-carrier vanishing and
currentLocalEval_ofReal rather than duplicating a long coordinate calculation.

## Part H — selected factor is the quotient-side real factor

Using Part E and

    directOrbitQuotient p =
      seventhQuotient (rotateEquiv p.rho) p.rho,

prove the three-factor identity

    product over i : Fin 3 of currentRealPairCarrier i rho1 rho0
      = directOrbitQuotient p.

Prove that the selected factor lies in the quotient prime Q.

If clean, prove the other two factors do not lie in Q.

Preferred route:

- evaluate them in ZMod q;
- divide by evalReal rho0^2;
- reduce to the three distinct values
    1 + tau^j + tau^-j;
- use the existing current phase-distinctness machinery.

If this non-membership proof becomes disproportionate, record it as the next
local frontier rather than introducing heavy algebra.

## Part I — exact degree-six prime pair over the selected real prime

Reuse/refactor the neutral part of the historical conjugate-prime-pair proof
for CurrentMuSevenResidueAddress.

Target:

    Ideal.map ofReal (RingHom.ker c.address.evalReal)
      =
    c.address.currentKernel *
      c.address.conjugate.currentKernel.

The current modules already provide:

- both kernels maximal;
- distinctness;
- common real contraction.

The missing reverse containment should be the same quadratic-coordinate
argument used historically and should not require signed-root provenance.

Promote a neutral theorem on CurrentMuSevenResidueAddress if clean.

This is the preferred second mandatory endpoint.

## Part J — current principal-ideal ownership

From Parts D/I derive the first current ownership statements:

    c.address.currentKernel
      divides Ideal.span {currentLinearCarrier c}

and

    c.address.conjugate.currentKernel
      does not divide Ideal.span {currentLinearCarrier c}

in the mathematically correct ideal-divisibility orientation.

Similarly for the conjugate carrier.

Do not yet claim exact multiplicity unless proved.

## Part K — local multiplicity audit

Audit whether the exact exponent at the quotient real prime Q can already be
read from current data.

Available structure:

    directOrbitQuotient p
      = eisensteinAxis^3 *
          quotientUnit *
          quotientRoot^7

and

    quotientRoot
      = quotientSquareUnit *
          quotientSquareRoot^2.

For q != 7 this suggests a multiple-of-14 exponent at Q.

Determine what is already kernel-checkable:

1. Q does not contain eisensteinAxis.
2. quotient unit factors are units.
3. the Q-adic multiplicity of directOrbitQuotient equals
       14 * multiplicity of quotientSquareRoot.
4. if Parts H selects exactly one real-pair factor at Q, its multiplicity is
   that same multiple of 14.
5. via Part I/J, the oriented degree-six linear carrier inherits the complete
   exponent at currentKernel while its conjugate exponent is zero.

Do not manufacture a valuation theorem if the required Dedekind
factorization API is not already available.

If exact multiplicity is feasible, expose a theorem of the form:

    exists e > 0,
      currentKernel^(14*e) divides span {currentLinearCarrier c}

together with non-divisibility by the next power if obtainable.

## Part L — compare against historical valuation ownership

Create a reuse ledger for
SevenRamifiedFusionOrientedCarrierValuationOwnership.

Classify each ingredient:

Reusable neutral:

- quadratic carrier coordinates;
- current/conjugate kernel pair algebra;
- coprimality of the two kernels;
- exact carrier/conjugate membership;
- ideal product/contraction arguments.

Historical-provenance only:

- RamifiedSignedRootRoutingPacket;
- old load families;
- historical quotientExponent;
- loaded residual/core factorization;
- terminal FUSION conclusions.

Do not instantiate a historical terminal packet with current witnesses merely
because the types look similar.

## Part M — exact next frontier

If Parts A-J are green but no contradiction follows, state the new C>1
frontier exactly.

Preferred formulation:

At every common q >= 379, current provenance canonically selects:

- one real prime Q above q;
- two conjugate degree-six primes K and Kbar over Q;
- an oriented linear carrier L with
      L in K, L notin Kbar;
- its conjugate Lbar with the opposite ownership;
- L*Lbar equal to the selected real-pair factor of directOrbitQuotient.

Then the next genuinely global theorem must couple these local oriented
ownership choices across all common primes, likely through:

- a principal-ideal seventh-power statement;
- a class-number-one principalization;
- or a global cyclotomic unit/character constraint.

Do not start that global theorem in R62 unless it falls out immediately.

## Hard stops

- No historical signed-root terminal contradiction.
- No claim that the current phase index is always zero.
- No replacement of ratio=tau^m by ratio=tau unless m=1 is proved.
- No arbitrary choice of zeta orientation; use phaseInverseExponent.
- No q % 28 resurrection.
- No real Kummer condition claimed to distinguish ratio/inverse.
- No exact prime multiplicity without a kernel-checked factorization proof.
- No external reciprocity/class-field theorem as axiom.
- No C=1 Thomas work.
- No final FLT7 theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:

- current phase-corrected linear-carrier production module;
- neutral current real-pair factorization module if clean;
- current conjugate-prime fibre equality if Part I succeeds;
- report-068.md;
- ROADMAP.md.

Add facade/API/axiom audits for reusable public results.

## Outcomes

- Outcome A — phase-corrected carrier, real-pair factorization, exact
  current/conjugate prime ownership, fibre equality, and a multiple-of-14
  local multiplicity theorem are all kernel-checked.
- Outcome B — carrier construction, selected real-pair factor, ownership, and
  current/conjugate fibre equality are green; exact multiplicity is the next
  frontier.
- Outcome C — carrier construction and local orientation are green, but the
  fibre equality or selected-factor uniqueness remains.
- Outcome D — phase correction does not produce the expected linear carrier;
  document the corrected degree-six geometry.
