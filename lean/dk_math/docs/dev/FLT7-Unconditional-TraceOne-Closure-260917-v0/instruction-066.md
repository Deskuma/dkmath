# FLT7TC-005R60 — Coefficient-ratio phase collapse and quotient/gap orientation bit

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-065.md
- SevenRealCubicCurrentCommonPrimePacket.lean
- SevenRealCubicCurrentOrientedGapTransport.lean
- SevenRealCubicCurrentCyclotomicFourteen.lean
- SevenRealCubicCurrentCoefficientRatios.lean
- PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean
- PrimeTraceOneDirectRealCubicSquareIdealSupport.lean
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean

R59 completed:
- current quotient-side residue/cyclotomic packet;
- exact order-seven phase-normalized address;
- current/conjugate degree-six kernels;
- fixed-ZMod oriented gap-prime transport f0/f1/f2;
- neutral fourteen-power zero-index lemmas;
- generic coefficient ratios R0,R1,R2 and R0*R1*R2=-1.

R60 must decide the I1/I2 transport question.

The expected outcome from the exact coefficient transport algebra is I2:
the three local fourteen-power relations collapse to one oriented residue class.
This expectation must be kernel-checked, not assumed.

## Part A — package the actual current coefficient ratios

For t := h.squareRefinement, define:

    c0 := directOrbitSquareTwistCoeff0 t
    c1 := directOrbitSquareTwistCoeff1 t
    c2 := directOrbitSquareTwistCoeff2 t

and the three SevenRealCubic units:

    R0 := currentCoefficientRatio0 c0 c1 c2 = -c2/c1
    R1 := currentCoefficientRatio1 c0 c1 c2 = -c0/c2
    R2 := currentCoefficientRatio2 c0 c1 c2 = -c1/c0.

Expose a current packet or definitions tied to h/t.

Prove again as a specialized corollary:

    R0 * R1 * R2 = -1.

Identify R0 exactly with directOrbitCommonPrimeTwistRatio21 t.

Do not leave this only as a simp-level heuristic; expose an exact theorem.

## Part B — cyclic norm of the transport multiplier

Let

    P := directOrbitPairAxisUnitOne
    e := 32 + 42*t.powerSplit.gapSplit.k
    A := P^e.

From the existing coefficient transport:

    c1 = A * rotate(c0)
    c2 = A * rotate(c1).

Prove the cyclic norm identity for P:

    P * rotate(P) * rotate^2(P) = 1.

A direct norm theorem for P is acceptable if already available.

Then prove:

    A * rotate(A) * rotate^2(A) = 1.

Do not use projectiveLog for this exact identity.

## Part C — close the third coefficient transport

From Part B and the two existing transport theorems prove:

    rotate(c2) = A^-1 * c0.

Equivalent orientations are acceptable.

Then prove the exact cyclic ratio laws:

    rotate(R0) = R1
    rotate(R1) = R2
    rotate(R2) = R0.

Prefer unit-level equalities first, then value-level corollaries.

This is the key algebraic theorem of R60.

## Part D — complete the fixed-ZMod zero pattern

R59 already proves:
    f0(r0)=0
    f0(r1)!=0
    f0(r2)!=0
    f1(r1)=0
    f1(r2)!=0
    f2(r2)=0.

Complete all missing nonzero facts, in particular:
    f1(r0)!=0
    f2(r0)!=0
    f2(r1)!=0.

Use only the definitions fi = f0 o rotate^{-i} and the original f0 pattern.

Package the complete 3x3 zero/nonzero table.

## Part E — instantiate the three fourteen-power relations

Apply f0, f1, f2 to directOrbit_squareTwist_twisted_eq.

For each i prove an existential:

    exists y0 != 0, y0^14 = f0(R0)
    exists y1 != 0, y1^14 = f1(R1)
    exists y2 != 0, y2^14 = f2(R2).

Use the neutral zero-index lemmas from R59.

Keep the quotient-side cyclotomic evaluation completely separate here.

## Part F — decisive phase collapse

Using Part C and the transport identities

    f1(rotate x) = f0(x)
    f2(rotate^2 x) = f0(x),

prove exactly:

    f1(R1) = f0(R0)
    f2(R2) = f0(R0).

Therefore all three fourteen-power statements are copies of the same statement:

    exists y != 0, y^14 = f0(R0).

Expose a theorem conceptually named:

    currentCommonPrime_fourteen_phase_collapse.

This is the preferred Outcome B theorem.

## Part G — formally reject the naive mod-28 multiplication

Do NOT prove a meta-level "not derivable" statement.

Instead package the concrete obstruction:

    transported_rhs0 = transported_rhs1
    transported_rhs1 = transported_rhs2.

Together with
    R0*R1*R2 = -1

show explicitly that the product of the transported RHS values is

    f0(R0)^3

rather than

    f0(R0*R1*R2) = -1.

Record why:
transporting Ri from its own rotated prime applies rotate^{-i} to Ri, hence
all become R0 before evaluation.

If useful prove:

    f0(R0) * f1(R1) * f2(R2) = f0(R0)^3.

Do not assert any q % 28 consequence.

Update ROADMAP/report to mark the naive mod-28 route CLOSED/INVALID under exact
Galois transport.

## Part H — quotient-side prime is not the gap prime

Let:
- P0 be the oriented gap prime from CurrentOrientedGapPrimeTransport;
- Q be the quotient-side prime from CurrentCommonPrimeResiduePacket.

Prove:

    Q != P0.

Preferred route:
- gapSquareRoot lies in P0;
- quotientSquareRoot lies in Q;
- the two principal ideals / roots are coprime;
- if Q=P0 then the prime contains both, contradicting coprimality.

Reuse directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers.

Do not infer equality/non-equality merely from separately chosen finite-field
equivalences.

## Part I — classify Q inside the three-prime Galois orbit

Define the two conjugate gap primes:

    P1 := sigma • P0
    P2 := sigma^2 • P0

with the repository's actual action convention.

Prove:
- P0,P1,P2 are pairwise distinct;
- each lies over q;
- every prime over q is one of P0,P1,P2.

Use:
    common_norm_prime_complete_split
and
    directOrbitGalois_prime_orbit_eq_primesOver
or the cleanest existing Galois API.

Then Part H gives:

    Q = P1 or Q = P2.

Package this as the current quotient/gap orientation dichotomy.

This is the mandatory second endpoint of R60.

## Part J — connect the orientation dichotomy to the quotient tau phase

Do not try to decide Q=P1 versus Q=P2 unless current data really do.

Audit how the quotient-side evaluation

    evalReal_Q

relates to f1 or f2 after choosing compatible residue-field equivalences.

Because the finite-field equivalences were chosen independently, direct map
equality is not canonical.

Instead look for an invariant statement:
- the quotient tau is one of a gap-side primitive root and its inverse;
- the phase index changes by k -> 3-k;
- or the two alternatives exchange the current/conjugate degree-six kernels.

State only an equivalence-invariant theorem unless a canonical equivalence is
constructed.

## Part K — next independent global obstruction

After phase collapse, identify the smallest genuinely NEW theorem needed on C>1.

Preferred candidates to audit:

1. A character/reciprocity relation comparing quotient-side and gap-side
   degree-six prime addresses.
2. A global principal-ideal relation coupling both orientations at the same q.
3. A quadratic character of the Kummer unit beta(1+beta) that is sensitive to
   Q=P1 versus Q=P2.

Do not begin a full reciprocity formalization in R60.

The report should state the exact input/output signature of the best next
theorem.

## Hard stops

- No q % 28 theorem.
- No multiplication of untransported residue statements from different primes.
- No arbitrary residue-field equivalence treated as Galois-canonical.
- No historical terminal contradiction.
- No external reciprocity theorem as an axiom.
- No C=1 Thomas work.
- No FLT7 final theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:
- current coefficient-ratio rotation/collapse module;
- quotient/gap prime-orientation module;
- report-066.md;
- ROADMAP.md.

Add facade/API/axiom tests for clean reusable public theorems.

## Outcomes

- Outcome A — contrary to expectation, exact transport yields independent
  residues; document the corrected algebra before any mod-28 claim.
- Outcome B — phase collapse is kernel-checked and Q=P1 or Q=P2 is
  kernel-checked; naive mod-28 route is closed and the orientation bit is the
  precise C>1 frontier.
- Outcome C — phase collapse is green, but quotient/gap prime orbit
  classification remains.
- Outcome D — coefficient ratios do not rotate cyclically as expected; record
  the exact correction factor and reassess transport.
