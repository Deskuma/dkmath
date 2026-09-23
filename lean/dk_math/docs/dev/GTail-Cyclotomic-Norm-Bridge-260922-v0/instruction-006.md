# GCNB-009A / instruction-006 — Generic conjugate-prime relative-norm ownership and R64 applicability gate

Branch: research/GTail-Cyclotomic-Norm-Bridge-260922-v0

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-005.md
- docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/GENERALIZATION_HANDOFF.md
- docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/CURRENT_STATE_FREEZE.md
- docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-070.md
- docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-071.md

Generic/current bridge references:

- DkMath/CFBRC/CyclotomicIdeal.lean
- DkMath/FLT/Prime/PrimeCyclotomicTraceOne.lean
- DkMath/FLT/Prime/PrimeCyclotomicCalibration.lean
- DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentPhaseCorrectedCarrier.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentSelectedFactorFiber.lean
- DkMath/FLT/Seven/SevenRealCubicCurrentSelectedFactorUniqueness.lean
- DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean

## 1. Mission

GCNB-001 through GCNB-008 have completed the generic scalar carrier stack:

~~~text
GTail / GN
  -> cyclotomic root product
  -> algebraic field norm
  -> principal ideal
  -> Ideal.absNorm
  -> rational-prime valuation
  -> generic FLT packet
  -> generic TraceOne scalar
  -> p = 3,5,7 scalar calibration
~~~

This does not yet solve the frozen FLT7 R64 obligation.

R64 already proves that the selected real factor has exact multiplicity

~~~text
14 * eQ
~~~

at its current real prime Q, including membership at that power and
nonmembership at the successor.

The missing deferred FLT7 statement is an exact upper cutoff for the
phase-corrected degree-six linear carrier in the selected oriented prime
kernel above Q.

GCNB-009A must extract the smallest genuinely reusable theorem that transports
an exact base-prime cutoff through a conjugate-pair / relative-norm identity.

Then instantiate that theorem in a test or scratch module against the frozen
R64 current-provenance data.

The FLT7 re-entry gate opens only if that specialization kernel-checks the
previously deferred current-carrier upper cutoff.

## 2. Why the existing absNorm theorem is not enough

Do not attempt to prove the R64 local cutoff merely from:

~~~text
padicValNat q (Ideal.absNorm I)
~~~

That is an aggregate rational-prime valuation and may sum contributions from
several prime ideals above q with residue-degree weights.

R64 needs ownership at one selected degree-six prime ideal.

Likewise, the current R64 carrier is not literally the natural-coordinate
element

~~~text
(g+u) - u*zeta
~~~

It is of the form

~~~text
rotate(rho) - zeta_phase * rho
~~~

with coefficients in the real cubic subring.

Therefore GCNB-009A is a relative norm / conjugate prime ownership checkpoint,
not another GN polynomial theorem.

## 3. Existing successful proof shape to generalize

The historical production theorem

~~~text
carrier_not_mem_orientedKernelPower_succ
~~~

in

~~~text
DkMath.FLT.Seven.SevenRamifiedFusionOrientedCarrierValuationOwnership
~~~

already demonstrates the relevant argument.

Its structure is:

~~~text
assume alpha in P^(m+1)

star transport:
  star(alpha) in Pbar^(m+1)

multiply:
  alpha * star(alpha)
    in P^(m+1) * Pbar^(m+1)

identify pair product:
  alpha * star(alpha) = map(beta)

identify paired prime powers:
  P^(m+1) * Pbar^(m+1) = map(Q^(m+1))

contract through the extension:
  beta in Q^(m+1)

contradict:
  beta notin Q^(m+1)
~~~

Extract this logic instead of rebuilding a large valuation theory.

## 4. Preferred generic theorem: upper-cutoff transport

Prefer a theorem whose hypotheses explicitly expose only the algebraic facts
the proof consumes.

A conceptual shape is:

~~~lean
theorem not_mem_primePower_succ_of_conjugate_norm_cutoff
    {A B : Type*}
    [CommRing A] [CommRing B]
    (f : A ->+* B)
    (Q : Ideal A)
    (P Pbar : Ideal B)
    (alpha alphaBar : B)
    (beta : A)
    (m : Nat)
    (hstarMem :
      alpha ∈ P^(m+1) -> alphaBar ∈ Pbar^(m+1))
    (hpair : alpha * alphaBar = f beta)
    (hmapPow :
      Ideal.map f (Q^(m+1)) = P^(m+1) * Pbar^(m+1))
    (hcontract :
      Ideal.comap f (Ideal.map f (Q^(m+1))) = Q^(m+1))
    (hBetaNot : beta ∉ Q^(m+1)) :
    alpha ∉ P^(m+1)
~~~

This is only a conceptual shape. Use the smallest stable statement supported by
the pinned APIs.

It is acceptable, and probably preferable, to avoid abstracting the star
operation itself. The theorem may simply receive the exact membership transport
hypothesis from alpha to alphaBar.

Likewise, if the paired ideal-power map identity is easier to supply directly
as a hypothesis, do that.

The goal is a small ownership lemma, not a universal theory of involutions,
Dedekind extensions, or valuations.

## 5. Recommended neutral placement

Prefer:

~~~text
DkMath/Lib/NumberTheory/ConjugatePrimeIdealOwnership.lean
~~~

or another clearly neutral NumberTheory/Lib location consistent with existing
dependency rules.

The production generic module must not import DkMath.FLT and must not mention
p = 7, SevenRealCubicInt, SevenCyclotomicDegreeSixInt, currentLinearCarrier,
selectedRealPairCarrier, eQ, or FLT7 in theorem statements or implementation.

A generic theorem that merely happens to be motivated by FLT7 is acceptable.

## 6. Faithfully-flat contraction

Audit and reuse the exact pinned theorem already used by the historical proof:

~~~text
Ideal.comap_map_eq_self_of_faithfullyFlat
~~~

if the generic setup naturally supports it.

Do not add a new axiom saying contraction is injective if the existing
faithfully-flat algebra theorem suffices.

However, if making the theorem fully typeclass-generic would make it brittle,
it is acceptable for the ownership lemma to take the exact contraction
identity as an explicit hypothesis:

~~~text
Ideal.comap f (Ideal.map f (Q^k)) = Q^k
~~~

That keeps the lemma reusable while allowing downstream carriers to discharge
faithful-flatness in their own preferred way.

## 7. Do not require global unique factorization unless necessary

The upper-cutoff contradiction should ideally use only ideal membership,
map/comap, multiplication, and conjugation transport.

Do not introduce UniqueFactorizationMonoid on ideals, Associates.count,
class-group assumptions, or PID assumptions unless the proof genuinely cannot
avoid them.

R64 already has its exact base cutoff. The generic theorem's job is only to
transport that cutoff upstairs.

## 8. Optional exact-cutoff wrapper

If the generic upper-cutoff theorem is clean, add a thin wrapper:

~~~text
alpha in P^m
alpha notin P^(m+1)
--------------------
alpha in P^k <-> k <= m
~~~

using monotonicity of ideal powers.

Do not make this wrapper the hard part of the checkpoint.

The essential new theorem is the successor nonmembership transport.

## 9. Mandatory R64 applicability probe

This is the decisive part of the checkpoint.

Do not modify the closed FLT7 production tower.

Add a test or scratch file on the current branch, for example:

~~~text
DkMathTest/FLT/Prime/CurrentCarrierOwnershipProbe.lean
~~~

or:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/scratch-006-r64-ownership.lean
~~~

It may import the frozen FLT7 modules because it is a consumer/probe, not
neutral production infrastructure.

Instantiate the generic ownership theorem with the current R64 data.

Conceptually:

~~~text
A     = current real cubic integral carrier used by Q
B     = SevenCyclotomicDegreeSixInt.Ring

beta     = selectedRealPairCarrier c
alpha    = currentLinearCarrier c
alphaBar = currentConjugateLinearCarrier c

Q     = c.residue.Q
P     = c.address.currentKernel
Pbar  = c.address.conjugate.currentKernel

m     =
  14 *
    currentIdealPrimeMultiplicity
      c.residue.Q
      (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot)
~~~

Reuse existing R64 facts, especially:

~~~text
currentLinearCarrier_mul_conjugate
currentLinearCarrier_mem_currentKernel
currentConjugateLinearCarrier_mem_conjugateKernel
currentLinearCarrier_not_mem_conjugateKernel
currentConjugateLinearCarrier_not_mem_currentKernel

selectedRealPairCarrier_mem_Q_pow
selectedRealPairCarrier_not_mem_Q_pow_succ

realPrimeFiberIdeal / current fibre equality
~~~

and any existing map-of-real / kernel product theorem that identifies the
extension of Q with the current/conjugate degree-six pair.

### Mandatory target

The probe must derive the previously deferred shape:

~~~text
currentLinearCarrier c ∉
  c.address.currentKernel ^ (m + 1)
~~~

from the new generic theorem, not by calling a pre-existing FLT7 theorem that
already states the same cutoff.

If a lower-bound theorem is already available for the current carrier, combine
it with the new upper bound and optionally prove:

~~~text
currentLinearCarrier c ∈ c.address.currentKernel ^ k
  <-> k <= m
~~~

But the mandatory success criterion is the new upper cutoff.

## 10. Existing abstract-to-concrete p=7 carrier map

Audit, and reuse if relevant:

~~~text
SevenCyclotomicDegreeSixInt.ringOfIntegersToRing :
  O (CyclotomicField 7 Q) ->ₐ[Z]
    SevenCyclotomicDegreeSixInt.Ring

ringOfIntegersToRing_surjective
ringOfIntegersToRing_injective
~~~

This confirms that the explicit degree-six carrier is not an unrelated ring.

However, do not force the new generic theorem through the abstract
CyclotomicField representation if the relative real-cubic extension is the
natural proof domain for R64.

The current carrier has real-cubic coefficients, so the successful
specialization may naturally live in the explicit quadratic extension.

## 11. Stop rules for the applicability probe

If the R64 probe fails, stop and report the first genuine missing bridge.

Examples of valid blockers:

- no checked identity of the form
  Ideal.map ofReal (Q^k) = P^k * Pbar^k
  for the current Q/P/Pbar;
- current fibre equality exists only at k=1 and cannot be promoted to powers
  without an additional theorem;
- faithful-flat contraction is unavailable for the current extension;
- conjugation does not map the current kernel power to the conjugate kernel
  power through an existing API;
- the selected real factor exact cutoff is expressed in a different ring of
  integers with no checked ideal transport;
- the current linear carrier pair-product equality cannot be expressed through
  the same algebra map used by ideal extension.

Do not patch these by adding FLT7-specific assumptions to the generic
production theorem.

Record the blocker exactly.

## 12. Outcome policy

### Outcome A — generic theorem genuinely reopens FLT7

All of the following must hold:

1. a neutral reusable upper-cutoff ownership theorem is production code;
2. focused and full builds are green;
3. a scratch/test-only R64 specialization proves the missing current
   degree-six carrier successor nonmembership using that generic theorem;
4. no closed FLT7 production file is modified;
5. no terminal contradiction or final FLT7 theorem is claimed here.

If Outcome A is achieved, mark the FLT7 re-entry gate OPEN and write a handoff
for a new FLT7 branch.

### Outcome B — useful generic theorem, R64 specialization blocked

The neutral theorem is valid and reusable, but one concrete current-provenance
map/fibre/contraction fact is missing.

Keep the re-entry gate closed and record the exact missing bridge.

### Outcome C — no meaningful neutral extraction

If the only workable proof necessarily depends on the full specialized FLT7
packet structure, do not pretend it is generic.

Add no artificial abstraction. Record that the historical proof shape does
not currently factor into a useful neutral theorem.

## 13. No FLT7 production continuation here

Even under Outcome A, do not implement:

~~~text
global aggregation of current oriented degree-six factors
terminal contradiction
FLT7 theorem
~~~

in this branch.

This branch ends at the re-entry decision.

A successful Outcome A should produce only a handoff document naming the exact
new generic theorem and the exact R64 specialization theorem that justify a new
FLT7 branch.

## 14. Axiom / safety rules

No sorry, admit, sorryAx, new axiom, unsafe proof shortcut, or native_decide as
a theorem replacement.

The generic theorem must not smuggle the desired conclusion in as a
hypothesis.

In particular, do not assume alpha notin P^(m+1) in order to prove the same
statement.

## 15. Tests and audits

For the neutral theorem, include small synthetic tests if they help verify the
API.

For the R64 applicability probe:

- use the actual frozen current-provenance structures;
- prove the successor nonmembership target through the new generic theorem;
- add #print axioms for the generic public theorem and the probe theorem;
- do not use the historical exact-cutoff theorem as the proof.

If a theorem with the exact target already exists in an older historical
module, explicitly ensure the proof does not call it.

## 16. Validation

Run at least:

~~~text
lake build DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership
lake build <focused ownership test/probe target>
lake build DkMath.FLT.Prime
lake build DkMath
git diff --check
~~~

Adjust the first target if a different neutral module location is chosen.

Scan changed production/test/scratch files for prohibited constructs.

## 17. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-006.md
~~~

The report must contain:

- the final neutral theorem signature;
- the minimal algebraic hypotheses it consumes;
- whether faithful-flatness is internal or supplied as an explicit identity;
- the exact R64 objects used in the specialization;
- the exact R64 facts that discharge each generic hypothesis;
- the resulting successor nonmembership theorem if successful;
- an explicit FLT7 re-entry decision: OPEN or CLOSED.

## 18. Completion gate

The generalization campaign closes after this checkpoint.

The gate is:

~~~text
generic local ownership theorem
        +
actual R64 current specialization
        |
        v
previously deferred current degree-six upper cutoff
~~~

If the bottom theorem kernel-checks, re-entry is OPEN.

If it does not, re-entry remains CLOSED and the exact missing bridge becomes
the final recorded Gap of this branch.
