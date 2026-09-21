# FLT7TC-005R59 — Current cyclotomic constructor and exact Galois phase transport

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-064.md
- SevenRealCubicCurrentCyclotomicAddress.lean
- SevenRealCubicCurrentCyclotomicPhase.lean
- PrimeTraceOneDirectRealCubicCommonPrimeResidueOne.lean
- PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean
- PrimeTraceOneDirectRealCubicSquareIdealSupport.lean
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
- SevenRamifiedFusionCyclotomicConjugatePrimePair.lean

R58 outcome is C:
- neutral current cyclotomic address is green;
- phase-index theorem is green;
- current common-prime constructor is not yet packaged;
- exact Galois transport of the three fourteen-power relations remains open.

R59 must complete those missing bridges and decide the mod-28 question exactly.

Do not use historical signed-root terminal packets.

## Part A — expose the current quotient-side residue packet

Refactor the proof of common_norm_prime_mod_seven_one into a public packet
carrying the actual data that were previously local.

Preferred conceptual structure:

    structure CurrentCommonPrimeResiduePacket ... where
      q : Nat
      q_prime : q.Prime
      q_dvd_c : q | h.c
      Q : Ideal O
      Q_maximal : Q.IsMaximal
      Q_liesOver : Q.LiesOver (Ideal.span {(q : Z)})
      evalEquiv : Q.ResidueField ≃+* ZMod q
      evalReal : SevenRealCubicInt ->+* ZMod q
      quotientRoot_zero :
        evalReal t.quotientSquareRoot = 0
      quotient_zero :
        evalReal (directOrbitQuotient p) = 0
      rho_ne_zero :
        evalReal p.rho != 0
      rotate_rho_ne_zero :
        evalReal (rotateEquiv p.rho) != 0

Equivalent data organization is acceptable.

Construct it from:
- directOrbitCommonPrime_dvd_data;
- directOrbitSquareRefinement_exists_distinct_prime_ideals;
- common_norm_prime_complete_split;
- residueField_card_of_inertiaDeg_one.

Do not hide the finite-field equivalence needed later.

## Part B — expose the primitive seventh-root ratio

For a current residue packet define

    tau := evalReal (rotateEquiv p.rho) / evalReal p.rho

as a unit in ZMod q.

Prove:

    tau^7 = 1
    tau != 1
    orderOf tau = 7
    q % 7 = 1.

The proof should reuse the exact R48 argument, not call q % 7 = 1 backwards
to manufacture tau.

Package tau in the current residue packet or a thin extension packet.

## Part C — phase-normalized current cyclotomic address

Using alpha_cube under evalReal, prove

    evalReal alpha

satisfies

    X^3 - 2*X^2 - X + 1 = 0.

Apply current_phase_alignment tau to obtain

    k : Fin 3
    evalReal alpha = currentBeta tau (k.val+1).

Define

    ratio := tau^(k.val+1)

as a unit.

Prove:
- ratio^7 = 1;
- ratio != 1;
- orderOf ratio = 7;
- evalReal alpha =
    1 + ratio + ratio^-1.

For ratio != 1, use orderOf tau = 7 and the fact k.val+1 is one of 1,2,3.
A finite Fin-3 case split is acceptable.

Construct:

    CurrentMuSevenResidueAddress q

from this ratio.

This is the mandatory current constructor missing from R58.

Expose a public theorem:

    currentCommonPrime_cyclotomicAddress
      (h) (q) (hq) (hqc) :
      Nonempty (CurrentCommonPrimeCyclotomicPacket ...)

or an equivalent explicit existential.

The packet should carry:
- current residue packet;
- tau;
- phase index k;
- normalized ratio;
- CurrentMuSevenResidueAddress;
- currentKernel and conjugate.currentKernel.

## Part D — degree-six kernel pair for current provenance

From the current address prove:
- both degree-six kernels are maximal;
- their contractions to the real cubic order equal ker evalReal;
- the two kernels are distinct.

If the distinctness proof from the historical conjugate-prime module depends
only on ratio != ratio^-1, refactor/promote a neutral theorem.

Prove ratio != ratio^-1 from orderOf ratio = 7.

If practical, also promote the neutral real-prime fiber product identity:

    map ofReal (ker evalReal)
      = currentKernel * conjugate.currentKernel.

Only do this if the historical proof can be neutralized without importing
RamifiedSignedRootRoutingPacket.

## Part E — choose the current oriented gap prime and one base ZMod evaluation

For h and q | h.c, obtain the current oriented gap prime P0 from

    directOrbitCommonPrime_oriented_gap_prime.

Thus:
- gap root r0 lies in P0;
- rotate r0 and rotate^2 r0 do not lie in P0.

Use complete splitting/inertia degree one to choose once and for all

    e0 : P0.ResidueField ≃+* ZMod q

and define

    f0 : SevenRealCubicInt ->+* ZMod q.

Prove:
    f0(r0) = 0
    f0(r1) != 0
    f0(r2) != 0.

Do not identify this f0 with the quotient-side evalReal from Parts A-C unless
a theorem proves the kernels coincide. Keep the two real primes distinct.

## Part F — Galois transport inside one fixed ZMod q

Avoid arbitrary residue-field equivalences between P0,P1,P2.

Define three ring homs directly into the same ZMod q:

    f0(x) = base evaluation
    f1(x) = f0(rotateEquiv.symm x)
    f2(x) = f0(rotateEquiv.symm (rotateEquiv.symm x))

or the equivalent orientation consistent with the existing sigma action.

Kernel-check the exact transport law:

    fi(rotate^i x) = f0(x)

for i = 0,1,2.

Also prove the zero-pattern:

    f0(r0)=0, f0(r1)!=0, f0(r2)!=0
    f1(r1)=0, f1(r2)!=0, f1(r0)!=0
    f2(r2)=0, f2(r0)!=0, f2(r1)!=0.

This is the mandatory Galois-residue transport surface.

Be explicit about the action convention.

## Part G — neutral three-zero-index fourteen-power lemma

Promote a neutral field lemma for

    c0*r0^14 + c1*r1^14 + c2*r2^14 = 0

with nonzero c_i.

Prove:
- if r0=0:
      (r1/r2)^14 = -c2/c1
- if r1=0:
      (r2/r0)^14 = -c0/c2
- if r2=0:
      (r0/r1)^14 = -c1/c0.

Use division or units consistently.

Instantiate with f0,f1,f2 applied to the current square-twist equation.

## Part H — define the three global coefficient-ratio units

Define the three global SevenRealCubic units:

    R0 := -c2/c1
    R1 := -c0/c2
    R2 := -c1/c0

using the current square-twist coefficient units.

The existing R38 twist ratio is R0 up to exact naming/orientation.

Prove the exact global identity

    R0 * R1 * R2 = -1.

Also prove the Galois rotation relations among R0,R1,R2 if true:

    rotateEquiv R0 = R1
    rotateEquiv R1 = R2
    rotateEquiv R2 = R0

or record the corrected permutation/sign if the definitions differ.

Do not assume these relations before checking coefficient rotations.

## Part I — decisive transport computation

For each i, the local fourteen-power theorem gives

    exists yi != 0, yi^14 = fi(Ri).

Use Part F and the Part H rotation relations to rewrite every right-hand side
in terms of f0.

Determine exactly whether:

### I1 — independent product case
the transported values are
    f0(R0), f0(R1), f0(R2),

so their product is
    f0(-1) = -1.

Then prove -1 is a 14th power in ZMod q and derive q % 28 = 1.

The group-order argument must be fully kernel-checked.

### I2 — phase-collapse case
the transport identity gives

    fi(Ri) = f0(R0)

for all i, or another single oriented value.

Then prove this collapse explicitly.

In that case the three local fourteenth-power statements do NOT imply
that -1 is a fourteenth power, and the q % 28 route is invalid.

Do not choose I1 or I2 in advance.

This is the decisive R59 theorem.

## Part J — if I1 holds: residue-one-to-mod-28 strengthening

Only if I1 is proved, expose:

    directOrbitCommonPrime_q_mod_twentyEight_one
      (h) (q) (hq) (hqc) :
      q % 28 = 1.

Then derive:
- every common prime is 1 mod 28;
- c > 1 gives the corresponding smallest-prime lower bound;
- update the C>1 sharpened packet if the bound is cheap.

Check the actual smallest prime 1 mod 28 in Lean rather than assuming it.

## Part K — if I2 holds: permanently close the mod-28 mirage

If phase collapse is proved, add a report theorem/lemma showing exactly why
the cyclic-product identity cannot be multiplied across transported local
statements.

Keep:
- the current cyclotomic address;
- degree-six kernel pair;
- exact transport theorems.

Then state the next genuinely independent missing theorem:
likely a global character/reciprocity relation that couples distinct degree-six
prime addresses rather than transporting all of them to the same orientation.

## Part L — relation between quotient-side and gap-side current addresses

Audit whether the quotient-side real prime from Parts A-C and the gap-side
prime P0 from Part E are:
- distinct real primes above q;
- Galois conjugates;
- or can coincide under a specific phase.

Use the existing theorem that the gap and quotient square-root ideals are
supported on distinct primes.

If clean, package the exact relation. This may be useful for the next global
character step.

Do not force the two evaluations into one packet without proof.

## Hard stops

- No q % 28 claim unless Part I proves I1.
- No multiplication of residue statements from different primes before exact
  Galois transport.
- No arbitrary finite-field equivalence treated as Galois-compatible.
- No historical signed-root terminal contradiction.
- No reciprocity theorem invented.
- No C=1 Thomas work in R59.
- No FLT7 final theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:
- current common-prime cyclotomic constructor module;
- exact fixed-ZMod Galois transport module;
- report-065.md;
- ROADMAP.md.

Add facade/API/axiom tests for reusable production theorems.

## Outcomes

- Outcome A — current constructor and exact transport are green; I1 holds and
  q % 28 = 1 is proved.
- Outcome B — current constructor and exact transport are green; I2 phase
  collapse is proved, permanently ruling out the naive mod-28 route.
- Outcome C — current constructor is green, but fixed-ZMod Galois transport is
  the remaining frontier.
- Outcome D — the phase-normalized current address cannot be constructed from
  the R48 tau as proposed; document the corrected geometry.
