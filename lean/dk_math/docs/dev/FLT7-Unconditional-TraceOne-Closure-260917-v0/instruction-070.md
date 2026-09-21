# FLT7TC-005R64 — Selected-factor uniqueness and exact current 14e multiplicity

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Canonical checkpoint-document directory:

    docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/

Do NOT place new R64 report/instruction files under
lean/dk_math/docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/.

Repository hygiene at start:

- report-067.md exists in the canonical docs/dev directory.
- report-068.md exists in the canonical docs/dev directory.
- report-069.md currently exists under the old lean/dk_math/docs/dev path.
  Move/recreate report-069.md in the canonical docs/dev directory and remove
  the misplaced copy if that copy is part of this branch's diff.
- Preserve the mathematical content; do not rewrite history.

Authoritative production inputs:

- DkMath/FLT/Seven/SevenRealCubicCurrentSelectedFactorFiber.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentPhaseCorrectedCarrier.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentCommonPrimePacket.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentCyclotomicPhase.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentResidueKernel.lean
- DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareRefinement.lean
- DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareIdealSupport.lean
- DkMath/FLT/Seven/SevenRamifiedFusionPrimeLoadExactValuation.lean
- DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean

R63 endpoint:

- phase trace identity is green;
- selected real factor Fsel is defined;
- L * star(L) = ofReal(Fsel);
- Fsel evaluates to zero at the quotient evaluation and lies in Q;
- current real-prime fibre equality
      map(ker evalReal) = K * Kbar
  is green;
- first-power oriented/conjugate carrier ownership is green;
- uniqueness of Fsel among the three real factors is open;
- exact Q/K multiplicity is open.

R64 must first prove uniqueness, then exact multiplicity.
Do NOT import historical signed-root quotientExponent.

## Part A — pairwise distinct currentBeta phases

For an order-seven unit r in ZMod q, prove:

    currentBeta r 1 != currentBeta r 2
    currentBeta r 1 != currentBeta r 3
    currentBeta r 2 != currentBeta r 3.

Preferred assumptions:
    orderOf r = 7.

A direct algebraic proof is preferred:

- replace inverses by powers using r^7=1;
- factor an assumed equality;
- force r^d=1 for 1 <= d < 7;
- contradict orderOf r = 7.

Do not brute-force enumerate ZMod q.

Expose reusable public lemmas.

## Part B — exact evaluation table for currentCyclicAlpha

For

    c : CurrentCommonPrimeCyclotomicPacket h q

prove the evaluations of

    currentCyclicAlpha 0
    currentCyclicAlpha 1
    currentCyclicAlpha 2

are the three currentBeta values of c.tau, in the phase-dependent order.

At minimum prove:

    evalReal (currentCyclicAlpha (phaseTraceIndex c.phase))
      = currentBeta c.tau 1

and the two alternate indices evaluate to currentBeta c.tau 2 and 3
in some order.

A Fin 3 case split on c.phase and the factor index is acceptable.

## Part C — evaluation formula for each real pair factor

Let

    rho0 := p.rho
    rho1 := rotateEquiv p.rho.

Prove for every i : Fin 3 an explicit formula equivalent to

    evalReal (currentRealPairCarrier i rho1 rho0)
      =
    evalReal rho0 ^ 2 *
      (c.tau : ZMod q) *
      (currentBeta c.tau 1 -
        evalReal (currentCyclicAlpha i)).

Use:
    evalReal rho1 = tau * evalReal rho0
and
    evalReal rho0 != 0.

## Part D — selected-factor uniqueness

Using Parts A-C prove:

    c.residue.evalReal
      (currentRealPairCarrier i rho1 rho0) = 0
      <->
    i = phaseTraceIndex c.phase.

Then prove the ideal form:

    modelEquivRingOfIntegers
      (currentRealPairCarrier i rho1 rho0) ∈ c.residue.Q
      <->
    i = phaseTraceIndex c.phase.

Hence the quotient factorization

    F0 * F1 * F2 = directOrbitQuotient p

has exactly one factor supported at Q.

This is mandatory.

## Part E — minimal local ideal multiplicity API

Use the existing Associates/count pattern from
SevenRamifiedFusionPrimeLoadExactValuation.

Define only the small current-local helper needed, conceptually:

    idealPrimeMultiplicity P I :=
      (Associates.mk P).count (Associates.mk I).factors.

Do not create a broad new valuation library.

Prove/reuse:

- multiplicity is additive on ideal products;
- multiplicity of I^n is n times multiplicity of I;
- a unit principal ideal has multiplicity zero;
- if x notin prime P, the P-count of span{x} is zero;
- if x in P, the P-count is positive.

Prefer existing Associates.count lemmas.

## Part F — the quotient front factors are Q-units

Prove:

    eisensteinAxis ∉ Q.

Use q != 7 and norm_eisensteinAxis = -7.

Also record that:

- quotientUnit is a unit;
- quotientSquareUnit is a unit;
so their principal ideals contribute zero Q-multiplicity.

No historical beta-ne-three theorem is needed.

## Part G — exact quotient equality U * S^14

Let

    t := h.squareRefinement
    S := t.quotientSquareRoot.

From the existing exact equalities:

    directOrbitQuotient p
      = eisensteinAxis^3 * quotientCore

    quotientCore
      = quotientUnit * quotientRoot^7

    quotientRoot
      = quotientSquareUnit * S^2

derive a clean element theorem:

    exists U : SevenRealCubicIntˣ,
      directOrbitQuotient p =
        eisensteinAxis^3 * (U : SevenRealCubicInt) * S^14.

Or combine eisensteinAxis^3 separately if it is not a unit.

The Q-multiplicity consequence must be:

    mult_Q(span{directOrbitQuotient p})
      =
    14 * mult_Q(span{S}).

Set

    eQ := mult_Q(span{S}).

Prove:

    0 < eQ

from the current quotient-square-root support at Q.

This is mandatory.

## Part H — selected real factor gets all Q multiplicity

By Part D the other two real factors are not in Q, hence their Q-multiplicity
is zero.

Using

    F0 * F1 * F2 = directOrbitQuotient p

prove:

    mult_Q(span{selectedRealPairCarrier c})
      = 14 * eQ.

Then expose the exact cutoff:

    selectedRealPairCarrier c ∈ Q^k
      <->
    k <= 14 * eQ

or the equivalent ideal-divisibility statement.

In particular:

    selectedRealPairCarrier c ∈ Q^(14*eQ)

and

    selectedRealPairCarrier c ∉ Q^(14*eQ + 1).

## Part I — lift real multiplicity through the current fibre

Current fibre equality already gives:

    map(real kernel Q) = K * Kbar.

Use the selected factor product:

    L * Lbar = ofReal(Fsel)

with:

- L ∈ K;
- L ∉ Kbar;
- Lbar ∈ Kbar;
- Lbar ∉ K.

Generalize the historical oriented-ownership proof only as much as necessary.

Goal:

    L ∈ K^(14*eQ)
    L ∉ K^(14*eQ + 1)

and symmetrically:

    Lbar ∈ Kbar^(14*eQ)
    Lbar ∉ Kbar^(14*eQ + 1).

Do not use historical quotientExponent.
The exponent must be exactly the current 14*eQ.

Allowed strategy:

- map Q^k through ofReal;
- use fibre equality to obtain K^k * Kbar^k;
- combine L*Lbar = ofReal(Fsel);
- use coprimality of K and span{Lbar} to allocate the K^k factor to L;
- for the upper cutoff, mimic the historical star/contraction argument but
  with the current selected factor and current exponent.

If upper cutoff requires a missing faithful-flat contraction theorem already
available in the historical file, neutralize/reuse it; do not restate a
historical packet.

## Part J — current multiplicity packet

Package the local result for a current common prime q | c:

    structure CurrentCommonPrimeOrientedMultiplicityPacket ... where
      q
      q_prime
      q_ge_379
      eQ : Nat
      eQ_pos : 0 < eQ
      selectedIndex : Fin 3
      selectedFactor
      selectedFactor_unique
      realMultiplicity :
        mult_Q(span{selectedFactor}) = 14*eQ
      currentCarrier
      conjugateCarrier
      currentKernel
      conjugateKernel
      currentCarrier_cutoff
      conjugateCarrier_cutoff

Exact naming may differ.

Keep this packet current-provenance only.

## Part K — audit what global theorem is now missing

If Parts A-J are green, state the new exact frontier.

At every common q >= 379 we then have:

- a unique selected real factor;
- exact Q-exponent 14*eQ;
- two conjugate degree-six primes over Q;
- exact oriented carrier exponent 14*eQ on one half;
- exact conjugate exponent on the other half.

The next theorem is global, not local:
aggregate these oriented prime powers across all q | c into a principal ideal
statement for the current linear carrier or its residual quotient.

Audit whether existing generic Kummer/class-group infrastructure can express:

    span{L_global} = A^7

or

    span{L_global} = B^14

after removing unit/ramified factors.

Do not prove such a global statement in R64 unless it is immediate.

## Hard stops

- No historical signed-root terminal contradiction.
- No historical quotientExponent.
- No exact multiplicity inferred merely from first-power membership.
- No q % 28 route.
- No real Kummer orientation claim.
- No external reciprocity/class-field theorem as axiom.
- No C=1 Thomas work.
- No final FLT7 theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Canonical directory:

    docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/

Required document hygiene:

- report-067.md: retain; already canonical.
- report-068.md: retain; already canonical.
- report-069.md: place canonical copy here and remove misplaced branch copy if present.
- report-070.md: create here.
- ROADMAP update: use the existing project ROADMAP location unless the branch
  deliberately migrates it; do not create a second competing ROADMAP silently.

Production:

- selected-factor uniqueness theorem/module;
- exact current real multiplicity theorem;
- exact current degree-six carrier multiplicity if achievable;
- facade/API/axiom audits.

## Outcomes

- Outcome A — selected-factor uniqueness and exact real + degree-six 14e
  multiplicities are kernel-checked.
- Outcome B — selected-factor uniqueness and exact real 14e multiplicity are
  green; degree-six upper cutoff is the precise R65 frontier.
- Outcome C — uniqueness is green but exact real multiplicity still needs one
  explicit ideal-count lemma.
- Outcome D — the proposed beta/evaluation uniqueness formula is incorrect;
  record the corrected phase table before proceeding.
