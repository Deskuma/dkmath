# FLT7TC-005R61 — Orientation as ratio/inverse and Kummer-compatible prime sieve

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-066.md
- SevenRealCubicCurrentCommonPrimePacket.lean
- SevenRealCubicCurrentOrientedGapTransport.lean
- SevenRealCubicCurrentCoefficientPhaseCollapse.lean
- SevenRealCubicCurrentQuotientGapOrientation.lean
- SevenRealCubicCurrentCyclotomicPhase.lean
- PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicPrimeAllocation.lean

R60 outcome is B:

- the three fourteen-power relations collapse under exact Galois transport;
- the naive q % 28 route is closed;
- the quotient real prime satisfies exactly
      Q = sigma • P0  or  Q = sigma^2 • P0.

R61 converts this ideal-theoretic orientation bit into an explicit finite-field
ratio/inverse bit. Then it packages the surviving local Kummer condition as a
phase-independent support predicate and tests whether it sharpens the common
prime lower bound from 29 to 379.

No reciprocity theorem is assumed.

## Part A — uniqueness of ZMod-valued evaluation from the kernel

Prove a neutral reusable lemma:

    theorem zmod_ringHom_eq_of_ker_eq
        {R : Type*} [CommRing R]
        {q : Nat} [Fact q.Prime]
        (f g : R ->+* ZMod q)
        (hker : RingHom.ker f = RingHom.ker g) :
        f = g

Suggested elementary proof:
for x : R let n := (f x).val.
Then

    f (x - n) = 0

because (n : ZMod q) = f x.
Kernel equality gives

    g (x - n) = 0,

hence

    g x = (n : ZMod q) = f x.

Use ZMod.natCast_zmod_val.
Do not introduce quotient-ring equivalences unless they make the proof shorter.

This theorem is important: degree-one residue evaluations into the prime field
are canonical once their kernel is fixed.

## Part B — identify the kernels of f0/f1/f2 with P0/P1/P2

For

    b : CurrentOrientedGapPrimeTransport h q

define in O:

    P0 := b.P
    P1 := directOrbitGaloisSigma • P0
    P2 := directOrbitGaloisSigma^2 • P0.

Prove for every x : SevenRealCubicInt:

    b.f0 x = 0 <-> modelEquivRingOfIntegers x ∈ P0
    b.f1 x = 0 <-> modelEquivRingOfIntegers x ∈ P1
    b.f2 x = 0 <-> modelEquivRingOfIntegers x ∈ P2.

Use:

- b.f0_formula;
- directOrbitGaloisSigma_mem_iff;
- directOrbitGaloisSigma_model_rotate_mem_iff;
- directOrbitGaloisSigma_sq_model_mem_iff.

Package the corresponding kernel equalities on SevenRealCubicInt.

Likewise expose for

    a : CurrentCommonPrimeResiduePacket h q

the exact characterization

    a.evalReal x = 0 <->
      modelEquivRingOfIntegers x ∈ a.Q.

## Part C — canonical equality of quotient and gap evaluations

Using Part A/B and the R60 orientation theorem prove:

if

    hQ1 : a.Q = directOrbitGaloisSigma • b.P

then

    a.evalReal = b.f1.

If

    hQ2 : a.Q = directOrbitGaloisSigma^2 • b.P

then

    a.evalReal = b.f2.

Expose a dichotomy carrying map equality, not merely prime equality:

    a.evalReal = b.f1  or  a.evalReal = b.f2.

This removes the independently-chosen residue-field-equivalence ambiguity.

## Part D — the gap equation vanishes at f0

Let rho0 := p.rho,
    rho1 := rotateEquiv p.rho,
    rho2 := rotateEquiv (rotateEquiv p.rho).

Prove:

    b.f0 (directOrbitGap p) = 0.

Preferred route:

- expand the power-split/square-refinement factorization;
- b.gap_zero kills gapSquareRoot;
- all surrounding factors are irrelevant.

Then use

    directOrbitGap p = rho1 - rho0

to derive

    b.f0 rho1 = b.f0 rho0.

Prove both are nonzero.

For rho2, prove nonzero using the orientation dichotomy plus the quotient-side
nonzero fields:

- in Q=P1, a.rho_ne_zero becomes f0 rho2 != 0;
- in Q=P2, a.rotate_rho_ne_zero becomes f0 rho2 != 0.

Do not assume all orbit values are nonzero before proving this.

## Part E — define the gap-side primitive seventh root

Define

    deltaVal := b.f0 rho0 / b.f0 rho2

and bundle it as

    delta : (ZMod q)^x.

Using Part C/D prove the exact orientation law:

if Q=P1:
    a.tau = delta

if Q=P2:
    a.tau = delta^-1.

Check the action convention carefully.

Then prove unconditionally:

    delta^7 = 1
    delta != 1
    orderOf delta = 7.

It is acceptable to prove these by cases using
a.tau_pow_seven, a.tau_ne_one, and a.tau_orderOf.

This is the mandatory R61 orientation theorem.

## Part F — normalized cyclotomic ratio also becomes ratio/inverse

For

    c : CurrentCommonPrimeCyclotomicPacket h q

whose residue packet is a, let

    m := c.phase.val + 1
    gapPhaseRatio := delta^m.

Prove by the orientation cases:

    c.ratio = gapPhaseRatio
or
    c.ratio = gapPhaseRatio^-1.

Record the corresponding current/conjugate degree-six kernel interpretation.

Do not claim that the real trace distinguishes the two.

## Part G — neutral Kummer phase algebra

Define for a field-valued seventh-root unit r:

    phaseBeta r n :=
      1 + r^n + r^(-n)

or reuse currentBeta.

Define

    phaseKummer r n :=
      phaseBeta r n * (1 + phaseBeta r n).

For an order-seven unit r, prove the exact polynomial identities:

    phaseKummer r 2 * (1 + r)^7
      = - (phaseKummer r 1)^2

and

    phaseKummer r 3 * (1 + r^2)^7
      = - (phaseKummer r 2)^2.

A denominator-free proof is preferred.
These identities follow only from r^7=1 and r!=1.

Kernel-check all nonzero denominators/factors if division is used.

## Part H — seventh-power status is phase independent

In a field of characteristic not seven, for an order-seven unit r prove:

    (exists z, z^7 = phaseKummer r 1)
      <->
    (exists z, z^7 = phaseKummer r 2)

and similarly between phases 2 and 3.

Useful reverse-square extraction:
if x != 0 and x^2 = y^7, then

    x = (y^4 / x)^7.

Handle x=0 separately.

Thus all three phases have the same seventh-power-residue status.

Also prove inversion invariance:

    phaseKummer r^-1 n = phaseKummer r n.

Conclusion: the real-cubic Kummer condition cannot distinguish the
ratio/inverse orientation bit.

This is a mathematical theorem, not a meta-level statement.

## Part I — current common prime implies a normalized Kummer compatibility condition

From R60 obtain a nonzero fourteen-power witness

    y^14 = b.f0 R0,

where R0 is the current coefficient ratio.

Use the exact global correction

    R0 =
      directOrbitCommonPrimeKummerUnit * w^7

to derive a nonzero z with

    z^7 =
      b.f0 (directOrbitCommonPrimeKummerUnit : SevenRealCubicInt).

Let

    beta0 := b.f0 alpha.

Prove

    b.f0 KummerUnit = beta0 * (1 + beta0).

Since delta has order seven and beta0 satisfies the discriminant-49 cubic,
apply current_phase_alignment delta:

    exists j : Fin 3,
      beta0 = currentBeta delta (j.val+1).

Then use Part H to normalize the phase to 1.

Preferred public consequence:

    exists z : ZMod q, z != 0 and
      z^7 =
        phaseKummer delta 1.

## Part J — define a neutral Kummer-compatible-prime predicate

Define a finite predicate, conceptually:

    def SevenKummerCompatiblePrime (q : Nat) : Prop :=
      q.Prime and
      exists r : (ZMod q)^x,
        orderOf r = 7 and
        exists z : ZMod q,
          z != 0 and
          z^7 = phaseKummer r 1.

A more computation-friendly equivalent using the seventh-power criterion is
allowed.

Prove:

    q | h.c -> SevenKummerCompatiblePrime q.

Keep this theorem independent of C=1.

Also prove the predicate is independent of choosing r, if this is cheap.
It is not required for the current implication because Part I already
normalizes the concrete delta.

## Part K — finite sieve below 379

Research calibration indicates that the primes

    29, 43, 71, 113, 127,
    197, 211, 239, 281, 337

are exactly the primes q < 379 with q % 7 = 1, and none satisfies the
normalized Kummer compatibility condition. The first compatible calibration
prime is 379.

Do NOT trust this list as proof.

Kernel-check:

1. If q.Prime, q % 7 = 1, q < 379, then q is one of the ten listed values.
   A representation q = 7*k+1 followed by bounded interval_cases k is fine.

2. For each listed fixed q prove
       not (SevenKummerCompatiblePrime q).
   A finite by-decide proof is acceptable if it compiles reasonably.
   native_decide is forbidden.
   If direct existential search is too expensive, use the equivalent criterion
       K^((q-1)/7) != 1
   and enumerate only order-seven roots.

3. Optionally verify 379 is compatible as a calibration theorem, but do not
   make the main lower-bound theorem depend on this positive check.

Then prove:

    theorem sevenKummerCompatiblePrime_ge_379
      (hq : SevenKummerCompatiblePrime q) :
      379 <= q.

## Part L — strengthen the current common-factor packet

If Part K succeeds, expose:

    directOrbitCommonPrime_q_ge_379
      (h) (q) (hq) (hqc) :
      379 <= q.

Then prove:

    directOrbitCommonFactor_c_ge_379
      (h) (hc : 1 < h.c) :
      379 <= h.c.

Using the existing strict height

    h.c * h.u^5 < h.v

derive

    379 * h.u^5 < h.v.

Add this as a new sharpened C>1 theorem.
Do not mutate old APIs unnecessarily.

## Part M — exact frontier after the sieve

If the lower bound 379 is green, record:

C>1 now gives:

- every q | c is 1 mod 7;
- every q | c is Kummer-compatible;
- every q | c is >= 379;
- c >= 379;
- 379*u^5 < v;
- the quotient/gap orientation is ratio versus inverse;
- real Kummer data are inversion/phase blind.

Therefore the next genuinely new obstruction must live at the degree-six
or global level and distinguish the current/conjugate cyclotomic kernels.

Do not start reciprocity in R61.

## Hard stops

- No q % 28 theorem.
- No arbitrary residue-field equivalence treated as noncanonical after Part A:
  prove the same-kernel theorem first.
- No claim that Kummer phase invariance itself closes C>1.
- No external reciprocity/class-field theorem as an axiom.
- No unbounded computational search.
- No native_decide.
- No C=1 Thomas work.
- No final FLT7 theorem.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Deliverables

Primary:

- orientation-to-ratio/inverse production module;
- neutral Kummer-phase module;
- fixed finite sieve module if Part K succeeds;
- report-067.md;
- ROADMAP.md.

Add facade/API/axiom audits for reusable public results.

## Outcomes

- Outcome A — ratio/inverse orientation, phase-independent Kummer predicate,
  and the finite sieve are green; every current common prime is >=379.
- Outcome B — ratio/inverse orientation and Kummer phase invariance are green;
  the finite <379 sieve remains the only step.
- Outcome C — canonical evaluation equality is green, but the ratio/inverse
  formula or Kummer normalization remains.
- Outcome D — same-kernel ZMod uniqueness or the proposed orientation formula
  fails; record the corrected residue geometry.
