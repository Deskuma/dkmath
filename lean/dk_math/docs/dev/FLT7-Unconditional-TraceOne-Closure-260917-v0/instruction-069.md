# FLT7TC-005R63 — Selected real factor and current conjugate-prime fibre equality

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- SevenRealCubicCurrentPhaseCorrectedCarrier.lean
- SevenRealCubicCurrentCommonPrimePacket.lean
- SevenRealCubicCurrentCyclotomicAddress.lean
- SevenRealCubicCurrentResidueKernel.lean
- SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
- SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
- SevenRamifiedFusionCyclotomicAdditiveChartBoundary.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicPrimeAllocation.lean
- ROADMAP.md

Repository hygiene prerequisite:
At the start of R63, check whether these files exist on the branch:

- report-067.md
- report-068.md

They are referenced by ROADMAP but were not present in the branch state checked
after repeated fetches.

If absent, create them from the actual implemented theorem surfaces and the
ROADMAP summaries before writing report-069.md.
Do not invent unimplemented claims.

R62 outcome is C:

- phase inverse exponent is green;
- phase-corrected zeta is green;
- current/conjugate linear carriers are green;
- selected/opposite kernel membership and nonmembership are green;
- neutral three-real-factor product equals seventhQuotient;
- phase trace expansion and exact real-prime fibre equality remain open.

R63 must close those two bridges.

## Part A — exact phase trace identity

Current definitions:

    currentPhaseZeta c = zeta^(phaseInverseExponent c.phase)

    phaseTraceIndex 0 = 0
    phaseTraceIndex 1 = 2
    phaseTraceIndex 2 = 1

    currentCyclicAlpha 0 = alpha
    currentCyclicAlpha 1 = alpha^2 - 2*alpha
    currentCyclicAlpha 2 = -alpha^2 + alpha + 2.

Prove exactly:

    currentPhaseZeta c +
      zetaInv^(phaseInverseExponent c.phase)
      =
    ofReal (currentCyclicAlpha (phaseTraceIndex c.phase) - 1).

Equivalent star/inverse formulation is acceptable:

    currentPhaseZeta c + star (currentPhaseZeta c)
      =
    ofReal (currentCyclicAlpha (phaseTraceIndex c.phase) - 1).

A Fin-3 proof is preferred.

For the three cases kernel-check the concrete identities:

- zeta + zetaInv = ofReal (alpha - 1)
- zeta^4 + zetaInv^4 =
    ofReal (-alpha^2 + alpha + 1)
- zeta^5 + zetaInv^5 =
    ofReal (alpha^2 - 2*alpha - 1).

Use zeta^7=1 and the quadratic relation rather than external cyclotomic theory.

## Part B — selected real-pair factor

Define:

    selectedRealPairCarrier c :=
      currentRealPairCarrier
        (phaseTraceIndex c.phase)
        (rotateEquiv p.rho)
        p.rho.

Prove:

    currentLinearCarrier c *
      currentConjugateLinearCarrier c
      =
    ofReal (selectedRealPairCarrier c).

Prefer a short expansion using Part A and zeta*zetaInv=1.

Also prove the QuadraticAlgebra norm form:

    QuadraticAlgebra.norm (currentLinearCarrier c)
      = selectedRealPairCarrier c.

This is the exact current analogue of the historical oriented/conjugate carrier
product theorem.

## Part C — selected factor vanishes at the quotient evaluation

From Part B and

    currentLocalEval (currentLinearCarrier c)=0

prove:

    c.residue.evalReal (selectedRealPairCarrier c)=0.

Then using the current residue-kernel characterization prove:

    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈ c.residue.Q.

Expose both evaluation and ideal-membership theorems.

Do not prove membership by arbitrary identification with historical realPairCarrier.

## Part D — the other two real factors are nonzero at Q

Promote or prove a neutral phase-distinctness theorem for an order-seven unit r.

Let

    beta1 = 1 + r + r^-1
    beta2 = 1 + r^2 + r^-2
    beta3 = 1 + r^3 + r^-3.

Under orderOf r = 7 prove pairwise distinctness:

    beta1 != beta2
    beta1 != beta3
    beta2 != beta3.

The proof may use:

- finite exponent algebra from r^7=1 and r!=1;
- the three roots of X^3 - 2X^2 - X + 1;
- a Fin-3 finite decision after reducing to powers of one primitive root.

Do not use cardinality alone without explicit identification.

Then prove for i : Fin 3:

    c.residue.evalReal
      (currentRealPairCarrier i (rotateEquiv p.rho) p.rho) = 0
      <->
    i = phaseTraceIndex c.phase.

Consequently:

- exactly one of the three real factors lies in Q;
- the other two do not lie in Q.

This selected-factor uniqueness is mandatory if technically reasonable.

If the full iff becomes cumbersome, at minimum prove nonmembership for the two
explicit alternate indices by Fin-3 cases.

## Part E — quotient factor product revisited

Use the existing neutral theorem:

    currentRealPairCarrier_product

and

    directOrbitQuotient p =
      seventhQuotient (rotateEquiv p.rho) p.rho

to prove:

    currentRealPairCarrier 0 rho1 rho0 *
    currentRealPairCarrier 1 rho1 rho0 *
    currentRealPairCarrier 2 rho1 rho0
      =
    directOrbitQuotient p.

Then combine Part D to package:

    Q contains exactly one factor of this real three-factor decomposition.

This should become a reusable current packet.

## Part F — neutral current conjugate-prime fibre equality

Generalize the historical proof
CyclotomicLinearPrimeAddress.realPrimeFiberIdeal_eq_conjugateProduct
to CurrentMuSevenResidueAddress.

Define neutrally:

    def CurrentMuSevenResidueAddress.realPrimeFiberIdeal :=
      Ideal.map ofReal (RingHom.ker a.evalReal).

First prove:

    currentKernel ⊔ conjugate.currentKernel = top.

Use:

- both kernels maximal;
- currentKernel != conjugate.currentKernel.

Then prove the easy direction:

    realPrimeFiberIdeal <=
      currentKernel * conjugate.currentKernel.

Use:

- common real contractions;
- Ideal.mul_eq_inf_of_coprime.

For the reverse direction, port the explicit coordinate proof:

If x lies in both kernels then

    evalReal x.re + ratio * evalReal x.im = 0
    evalReal x.re + ratio^-1 * evalReal x.im = 0.

Subtract.
Since ratio != ratio^-1,

    evalReal x.im = 0,

then

    evalReal x.re = 0.

Finally reconstruct

    x = ofReal x.re + zeta * ofReal x.im

and conclude membership in the mapped real ideal.

Promote:

    theorem CurrentMuSevenResidueAddress.realPrimeFiberIdeal_eq_conjugateProduct :
      a.realPrimeFiberIdeal =
        a.currentKernel * a.conjugate.currentKernel.

This theorem must be completely independent of RamifiedSignedRootRoutingPacket.

## Part G — current packet specialization

For

    c : CurrentCommonPrimeCyclotomicPacket h q

specialize Part F:

    Ideal.map ofReal (RingHom.ker c.address.evalReal)
      =
    c.address.currentKernel *
      c.address.conjugate.currentKernel.

Then use the packet equality between address.evalReal and residue.evalReal to
rewrite this as the extension of the actual current quotient prime kernel.

If clean, prove an O-level theorem:

    Ideal.map (ofReal.comp modelEquivRingOfIntegers.symm.toRingHom) c.residue.Q
      = ...

or the repository's correct mapped-prime formulation.

Do not force this O-level statement if coercion noise obscures the clean model
kernel theorem; the model-level exact equality is already mandatory.

## Part H — carrier ideal divisibility ownership

From Part C/F prove:

    c.address.currentKernel
      divides Ideal.span {currentLinearCarrier c}.

For ideal divisibility orientation, verify the repository convention before
writing the theorem.

Likewise:

    c.address.conjugate.currentKernel
      divides Ideal.span {currentConjugateLinearCarrier c}.

Use the nonmembership theorems to record the opposite orientation:

    currentLinearCarrier c notin conjugate.currentKernel
    currentConjugateLinearCarrier c notin currentKernel.

Do not yet claim exact exponent one.

## Part I — q-adic multiplicity of the selected real factor

Audit the current quotient factorization at q != 7:

    directOrbitQuotient p
      = eisensteinAxis^3 *
          quotientUnit *
          quotientRoot^7

and

    quotientRoot
      = quotientSquareUnit *
          quotientSquareRoot^2.

The expected Q-adic contribution is a multiple of 14.

Before introducing a valuation theorem, audit existing Dedekind factorization
APIs for:

- Ideal.factorization;
- exponent of Q in a principal ideal;
- factorization of products and powers;
- unit principal ideals.

If the proof is short, establish:

    multiplicity_Q(span {directOrbitQuotient p})
      =
    14 * multiplicity_Q(span {quotientSquareRoot})

or an equivalent ideal-factorization theorem.

Then Part D implies the entire Q multiplicity sits in the selected real factor.

If this is not short, stop and record it as the exact R64 frontier.
Do not build a new general valuation framework in R63.

## Part J — degree-six multiplicity audit

If Part I is available, test whether fibre equality plus carrier ownership lets
the complete selected real-prime exponent choose exactly one degree-six half.

Important:
the equality

    map(Q) = K*Kbar

by itself gives an unordered pair.
The current linear carrier gives orientation, but exact multiplicity requires
a principal-ideal factorization of that carrier.

Audit whether the historical
SevenRamifiedFusionOrientedCarrierValuationOwnership
proof can be neutralized using only:

- fibre equality;
- carrier*conjugateCarrier = ofReal(selectedRealFactor);
- selected/opposite membership;
- comaximality.

If yes, prove an exact local theorem.
If no, report the precise missing lemma.

Do not reuse historical load exponents.

## Part K — exact C>1 frontier after R63

If Parts A-H are green, state the current local structure at every common
q >= 379:

- one selected real factor F_j of the quotient;
- one quotient prime Q containing exactly F_j;
- two conjugate degree-six primes K,Kbar above Q;
- a phase-corrected linear carrier L with
      L in K and L notin Kbar;
- star L with the opposite ownership;
- L*star L = ofReal(F_j);
- map(real kernel Q) = K*Kbar.

This is the complete local oriented geometry.

The next theorem is then not another residue sieve. It is an exact exponent /
principal-ideal ownership theorem, followed by a global aggregation of those
oriented local factors.

## Hard stops

- No historical signed-root terminal contradiction.
- No historical quotientExponent reused for current provenance.
- No exact multiplicity without a proved ideal factorization.
- No q % 28 resurrection.
- No real Kummer condition claimed to distinguish the two degree-six halves.
- No arbitrary phase simplification.
- No external class-field/reciprocity theorem as axiom.
- No C=1 Thomas work.
- No final FLT7 theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Repository hygiene:

- create report-067.md if still absent;
- create report-068.md if still absent.

R63:

- phase trace / selected-real-factor production module;
- neutral CurrentMuSevenResidueAddress fibre-equality theorem/module;
- selected-factor uniqueness if clean;
- report-069.md;
- ROADMAP.md.

Add facade/API/axiom audits for new public theorems.

## Outcomes

- Outcome A — phase trace, selected-factor uniqueness, neutral fibre equality,
  and an exact current local multiplicity theorem are kernel-checked.
- Outcome B — phase trace, selected-factor uniqueness, and neutral fibre
  equality are green; exact multiplicity is the precise R64 frontier.
- Outcome C — phase trace and selected-factor membership are green, but fibre
  equality or uniqueness remains.
- Outcome D — the expected phase trace index is wrong; document the corrected
  phase geometry.
