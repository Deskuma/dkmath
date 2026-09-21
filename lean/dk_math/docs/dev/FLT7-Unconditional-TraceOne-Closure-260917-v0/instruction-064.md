# FLT7TC-005R58 — Current common-prime cyclotomic phase transport audit

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative current inputs:
- report-054.md
- report-055.md
- report-063.md
- PrimeTraceOneDirectRealCubicCommonPrimeResidueOne.lean
- PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- PrimeTraceOneDirectRealCubicSquareIdealSupport.lean
- SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
- SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean
- SevenRamifiedFusionCyclotomicConjugatePrimePair.lean

Strategic position:

C=1 is now reduced to a fixed Thomas n=6 completeness theorem. R57 shows the
internal 7-adic route reaches a 7^8-th-power Thomas unit but does not yet
produce a strict successor.

R58 temporarily switches to C>1.

For every current common prime q | c, production already gives

    q prime
    q % 7 = 1
    q != 7
    q splits completely in the real cubic field
    one oriented gap prime
    a 14th-power residue condition
    a seventh-power Kummer residue condition.

Historical degree-six modules contain strong neutral cyclotomic algebra, but
their public packets are tied to the old RamifiedSignedRootRoutingPacket.
Do not import historical terminal conclusions into the current provenance.

R58 asks one precise question:

    Can the current common-prime residue data be lifted canonically to an
    oriented degree-six cyclotomic address, with exact Galois phase transport?

This checkpoint must also settle whether the tempting product argument

    twist * sigma(twist) * sigma^2(twist) = -1

really implies that -1 is a 14th power. Do not assume that it does.

## Part A — neutral current residue address

Create a neutral structure independent of historical signed-root routing,
conceptually:

    structure CurrentMuSevenResidueAddress (q : Nat) where
      prime : q.Prime
      evalReal : SevenRealCubicInt ->+* ZMod q
      ratio : (ZMod q)^x
      ratio_pow_seven : ratio^7 = 1
      ratio_ne_one : ratio != 1
      eval_alpha :
        evalReal alpha =
          1 + (ratio : ZMod q) + ((ratio^-1 : (ZMod q)^x) : ZMod q)

Exact naming may follow repository conventions.

Build all subsequent neutral degree-six evaluation theorems from this minimal
surface.

## Part B — neutral degree-six local evaluation

Reuse SevenCyclotomicDegreeSixInt.Ring and define, for a neutral address a,

    currentLocalEval a :
      SevenCyclotomicDegreeSixInt.Ring ->+* ZMod q

by

    ofReal x |-> a.evalReal x
    zeta     |-> a.ratio.

Prove:

    currentLocalEval_ofReal
    currentLocalEval_zeta.

The only well-definedness obligation is the quadratic relation

    ratio^2 - (evalReal alpha - 1)*ratio + 1 = 0,

which should follow immediately from eval_alpha.

Then define the two kernels selected by ratio and ratio^-1 and prove:
- maximality/surjectivity;
- distinctness;
- their contractions to the real cubic kernel coincide;
- their product is the mapped real-prime fiber ideal if the historical
  conjugate-prime proof can be generalized without signed-root data.

Prefer refactoring a neutral core out of the historical implementation to
duplicating long proofs.

## Part C — construct a current order-7 ratio

For a current canonical common-factor packet h and prime q | h.c, choose the
quotient-side real prime Q used in the R48 order-7 proof.

Reproduce/publicize the essential R48 data:

    f : SevenRealCubicInt ->+* ZMod q
    tau := f(rotateEquiv p.rho) / f(p.rho)
    tau != 0
    tau^7 = 1
    tau != 1.

Promote a packet carrying this data rather than hiding it inside
quotient_eval_mod_seven_one.

Do not derive q % 7 = 1 again except as a corollary.

## Part D — phase alignment with alpha

The current tau of Part C is a primitive seventh root, but it is NOT yet known
that

    f(alpha) = 1 + tau + tau^-1.

Audit the exact phase.

For k in {1,2,3}, define

    beta_k := 1 + tau^k + tau^(-k).

Kernel-check:
- each beta_k satisfies X^3 - 2X^2 - X + 1 = 0;
- beta_1, beta_2, beta_3 are pairwise distinct when q != 7;
- the polynomial factors as
      (X-beta_1)(X-beta_2)(X-beta_3).

Since f(alpha) satisfies the same cubic, prove

    exists k : Fin 3,
      f(alpha) = beta_(k+1).

This is the exact current phase-alignment theorem.

Do not assume k=1.

## Part E — current degree-six address

Using the chosen phase k, set

    ratio := tau^(k+1)

and construct CurrentMuSevenResidueAddress q.

Then construct the two current degree-six prime kernels over Q.

Expose:
- ratio has exact order 7;
- zeta maps to ratio;
- zetaInv maps to ratio^-1;
- the real contraction is the selected quotient-side prime;
- the two degree-six kernels are distinct.

This is the mandatory positive endpoint of R58.

## Part F — real-prime Galois orbit and canonical transport

Separately work with the current oriented gap prime P0 from

    directOrbitCommonPrime_oriented_gap_prime.

Define its two Galois translates P1,P2 under directOrbitGaloisSigma.

Prove exactly which one contains:

    gapSquareRoot
    rotate gapSquareRoot
    rotate^2 gapSquareRoot.

Construct residue-field equivalences induced by the Galois action, or
equivalent ring-hom transport maps.

Fix one base residue field / ZMod q evaluation and state exactly how evaluation
of a global element x at Pi transports back:

    eval_i(x) = eval_0(sigma^{-i}(x))

up to the repository's action convention.

This theorem must be explicit before any cyclic-product argument.

## Part G — neutral three-zero-index 14th-power lemma

Generalize the R38 computation.

Given in a field:
    c0*r0^14 + c1*r1^14 + c2*r2^14 = 0
with each c_i nonzero,

prove three variants:

if r0=0 and r1,r2 !=0:
    (r1/r2)^14 = -c2/c1

if r1=0:
    (r2/r0)^14 = -c0/c2

if r2=0:
    (r0/r1)^14 = -c1/c0.

Instantiate them at P0,P1,P2.

Define the three global coefficient-ratio units R0,R1,R2 and prove the exact
global identity

    R0 * R1 * R2 = -1.

If Astra's scratch theorem
twist_ratio_cyclic_product is still only scratch, promote the neutral exact
identity now.

## Part H — decisive phase-transport audit

Transport the three local 14th-power facts to ONE fixed residue field.

Determine exactly which global units they become after transport.

There are two possible outcomes:

H1. They become evaluations of three distinct cyclic ratios R0,R1,R2.
Then Lean may conclude

    -1 is a 14th power in F_q,

and therefore

    q % 28 = 1.

If so, prove q % 28 = 1 rigorously from the cyclic group order.

H2. Galois transport rotates both the prime and the coefficient ratio, so all
three statements collapse to the SAME oriented residue class.

If so, prove that collapse explicitly and record that the naive q % 28
argument is invalid.

Do not choose H1 or H2 in advance.

This is the main research question of R58.

## Part I — Kummer compatibility after phase alignment

For the selected current degree-six ratio, rewrite

    beta := f(alpha)
         = 1 + ratio + ratio^-1.

Translate the R38 Kummer condition

    z^7 = beta*(1+beta)

into a cyclotomic expression in ratio.

Kernel-check a compact factorization, for example forms derived from

    beta = (1 + ratio + ratio^2) / ratio
    1+beta = (1+ratio)^2 / ratio.

Record the exact unit/cyclotomic expression whose seventh-power residue is
forced.

Do not claim a contradiction from this alone.

## Part J — computational reconnaissance only

If H1 gives q % 28 = 1, test the combined local constraints on primes for
research guidance only.

Important: do not expect q % 28 plus the R38 Kummer condition to be universally
contradictory. Preliminary reconnaissance should explicitly search for
compatible primes before any theorem claim.

No computational result is production evidence.

## Part K — relation to historical degree-six tower

Produce a theorem-by-theorem reuse ledger:

Reusable neutral:
- SevenCyclotomicDegreeSixInt.Ring
- zeta/zetaInv algebra
- local evaluation algebra after neutralization
- conjugate degree-six prime pair
- fiber product ideal identities.

Historical-provenance only:
- RamifiedSignedRootRoutingPacket
- loaded-core packets
- global loaded factorization attached to old signed-root routes
- terminal fusion contradictions.

Do not instantiate historical terminal packets with current data by type
coercion tricks.

## Part L — report next closure route

If H1 is true:
- record q % 28 = 1 as a genuine strengthened common-prime support theorem;
- assess whether the cyclotomic Kummer expression has a reciprocity/character
  obstruction.

If H2 is true:
- close the mod-28 mirage permanently;
- keep the neutral current degree-six address as production infrastructure;
- identify the next genuinely independent global character/reciprocity theorem
  required.

## Hard stops

- No q % 28 theorem before Part H is kernel-checked.
- No use of arbitrary residue-field equivalences as if they preserved Galois
  orientation.
- No historical terminal FLT7 contradiction.
- No claim that q=379 is globally admissible or globally impossible merely
  from the old local calibration.
- No external reciprocity theorem as an axiom.
- No C=1 Thomas work in this checkpoint.
- No final FLT7 theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:
- a neutral/current degree-six residue-address module if Parts A-E are clean;
- a phase-transport scratch/production theorem for Parts F-H;
- report-064.md;
- ROADMAP.md.

Add facade/API/axiom tests only for genuinely reusable production theorems.

## Outcomes

- Outcome A — current degree-six address is green and phase transport proves
  q % 28 = 1.
- Outcome B — current degree-six address is green and phase transport proves
  the three 14th-power facts collapse to one oriented residue class; mod-28 is
  ruled out as a false route.
- Outcome C — neutral/current degree-six address is green, but exact Galois
  residue transport is the remaining frontier.
- Outcome D — current tau cannot be phase-aligned with alpha as proposed;
  document the corrected cyclotomic address geometry.
