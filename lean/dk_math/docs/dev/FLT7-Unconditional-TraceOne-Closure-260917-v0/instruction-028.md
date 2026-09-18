# FLT7TC-005R22 — Smaller-norm successor audit and cyclic twisted seventh-power state

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-027.md
- PrimeTraceOneDirectRealCubicOrbitGapHeight.lean
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicOrbit.lean
- astra-report-001.md

R21 now proves in production that every current direct real-cubic root packet
produces a positive strictly smaller integer norm.

This checkpoint does NOT assume that the smaller norm is already a new
CounterexamplePack or PrimitiveRamifiedSummitPacket.

Its purpose is to determine the correct successor state.

## Current production input

For current provenance, let:

    A := r.summit.gapRoot
    A = 7^k * a
    d0 := rotateEquiv rho - rho
    H0 := seventhQuotient (rotateEquiv rho) rho.

The production power split gives:

    d0 = theta^(32+42*k) * gapCore
    H0 = theta^3 * quotientCore

    gapCore = eta * g^7
    quotientCore = nu * h^7

with gapCore and quotientCore coprime.

The production height theorem gives:

    G := natAbs(norm g)
    0 < G
    G < a
    a <= A.

No successor state is currently constructed.

## Part A — exact norm complement of the two extracted roots

Define:

    G := Int.natAbs (norm g)
    Q := Int.natAbs (norm h).

Take absolute norms in:

    gapCore * quotientCore
      =
    orbitUnit01 *
      (thetaSevenUnit^(1+2*k) * (a : O)^2)^7.

Use:
- natAbs(norm eta) = 1;
- natAbs(norm nu) = 1;
- natAbs(norm orbitUnit01) = 1;
- natAbs(norm thetaSevenUnit) = 1;
- norm((a : O)^2) = a^6.

Prove exactly:

    (G * Q)^7 = a^42

and then, by injectivity of seventh powers on Nat,

    G * Q = a^6.

Expose this as a stable arithmetic theorem.

Do not infer coprimality of G and Q from element coprimality without a checked
norm/prime-support argument.

## Part B — rotate the exact gap split through all three edges

Let:

    rho0 := rho
    rho1 := rotateEquiv rho
    rho2 := rotateEquiv rho1

    g0 := g
    g1 := rotateEquiv g
    g2 := rotateEquiv g1.

Write e := 32 + 42*k.

From

    rho1-rho0 = theta^e * eta * g0^7

rotate twice and obtain literal equations for:

    rho2-rho1
    rho0-rho2.

Use:

    rotateEquiv theta = theta * pairAxisUnit 1

and its second iterate to rewrite all three edges with the SAME common factor
theta^e:

    rho1-rho0 = theta^e * eps0 * g0^7
    rho2-rho1 = theta^e * eps1 * g1^7
    rho0-rho2 = theta^e * eps2 * g2^7

where eps0, eps1, eps2 are explicit units.

The exact unit representatives may depend on eta, but they must be retained as
units rather than discarded.

Cancel theta^e from the telescoping identity:

    (rho1-rho0) + (rho2-rho1) + (rho0-rho2) = 0.

Prove the exact cyclic twisted equation:

    eps0 * g0^7 + eps1 * g1^7 + eps2 * g2^7 = 0.

This is the main successor candidate.

## Part C — coefficient class analysis

The projective class of eta was predicted by Astra-001 as (2,4) but was not
needed by the smaller-norm theorem and is not yet productionized.

Now audit whether it is needed to canonicalize the cyclic twisted state.

If needed, productionize:

    projectiveLog eta = (2,4)

in a generator-independent way.

Then compute the three coefficient classes:

    projectiveLog eps0
    projectiveLog eps1
    projectiveLog eps2

using the already checked Galois action on unit classes from Astra scratch.

The purpose is not to seek a contradiction from the three classes alone.
Astra already showed the old three-edge orbit classes are compatible.

The purpose is to determine whether, modulo seventh powers, every successor
candidate has ONE fixed canonical coefficient triple independent of the
original source.

If the coefficient triple can be normalized by seventh-power unit changes in
g0,g1,g2 to a fixed source-independent triple, construct that normalization.

If the eta class is not needed, explicitly record why.

## Part D — define the weakest honest successor candidate

Preferred shape, conceptually:

    structure DirectRealCubicTwistedSeventhState where
      root : SevenRealCubicInt
      root1 : SevenRealCubicInt
      root2 : SevenRealCubicInt
      coeff0 coeff1 coeff2 : SevenRealCubicIntˣ
      root1_eq_rotate : root1 = rotateEquiv root
      root2_eq_rotate : root2 = rotateEquiv root1
      twisted_eq :
        coeff0 * root^7 +
        coeff1 * root1^7 +
        coeff2 * root2^7 = 0
      root_norm_pos : 0 < natAbs (norm root)
      -- add only genuinely proved primitive/local conditions.

Construct this state from DirectOrbitSmallerNormPacket with:

    root := g

and retain the strict measure theorem:

    natAbs(norm root) < original gapRoot.

Do not include fields merely because they would be useful later.

## Part E — self-similarity audit

This is the decisive part.

Determine whether the new twisted state has enough structure to repeat the
same algebraic extraction and obtain another state with strictly smaller norm.

Audit, in order:

1. Can one form a natural "orbit gap" from root and rotateEquiv root?
2. Does the twisted equation force an exact theta depth for that new gap?
3. Is there a homogeneous seventh quotient with common-prime localization?
4. Can theta-free factors again be split as unit times seventh powers?
5. Is there a sign-free height identity giving a strict norm decrease?

If all five can be proved from the twisted-state fields alone, define a
successor map:

    next :
      DirectRealCubicTwistedSeventhState ->
      DirectRealCubicTwistedSeventhState

with

    measure (next s) < measure s

for measure := natAbs(norm s.root).

Only then formulate a well-founded contradiction/minimal-counterexample
consumer.

If any item fails, STOP at the first missing theorem and state exactly what
extra invariant the twisted state must retain.

Do not smuggle original integer endpoints back into the state unless they are
logically necessary.

## Part F — direct integer-summit reconstruction audit

Separately audit whether g or G can directly construct a new
PrimitiveRamifiedSummitPacket.

Recall that such a summit requires, among other data:

    L'^7 - R'^7 = D'^7
    L' - R' = 7^6 * A'^7
    cyclotomicSeven L' R' = 7 * B'^7
    D' = 7*A'*B'

plus endpoint coprimality, nonzero/seven-unit conditions and a TraceOne root
with exact norm.

Do NOT set A' := G and claim reconstruction.

For each required summit field, classify it as:

- already constructible from the smaller-norm packet;
- constructible if one explicit missing theorem is proved;
- currently unsupported.

If direct summit reconstruction is impossible with current data, record that
cleanly. That is a useful negative result.

## Part G — compare the two successor notions

At the end, answer:

1. Is the correct descent state the original integer ramified summit?
2. Is it the new real-cubic cyclic twisted seventh-power state?
3. Is a stronger hybrid state required?

Prefer the weakest state that is closed under a strict successor map.

The final goal is not to preserve historical packet shapes; it is to obtain a
noncircular well-founded descent from the current counterexample provenance.

## Hard stops

- Do not claim G is a new gapRoot merely because G < A.
- Do not claim a new CounterexamplePack without positive natural endpoints and
  a checked Fermat7Equation.
- Do not infer norm coprimality from element coprimality.
- Do not drop unit coefficients in the twisted equation.
- Do not use historical receiver/routing packets as successor assumptions.
- Do not claim infinite descent until a same-type successor map and strict
  measure theorem are both checked.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred implementation

Production only for facts that are clearly stable:
- exact norm complement G*Q=a^6;
- three rotated gap equations;
- telescoping twisted seventh-power equation;
- a minimal successor-candidate packet if honest.

Suggested file:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSuccessorAudit.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSuccessorAuditApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSuccessorAuditAxiom.lean

Create report-028.md and update ROADMAP.md.

## Report questions

1. Was G*Q=a^6 proved?
2. Were all three rotated gap splits written with one common theta^e factor?
3. Was the exact cyclic twisted seventh-power equation proved?
4. Were its unit coefficients explicit?
5. Was eta's projective class needed and, if so, productionized?
6. Is the coefficient triple canonical modulo seventh powers?
7. Was a minimal twisted successor candidate constructed with root g?
8. Can the extraction/height argument be repeated from that state alone?
9. Can g/G directly reconstruct a new PrimitiveRamifiedSummitPacket?
10. What is the exact first missing theorem for a genuine strict successor map?

## Outcomes

- Outcome A — SAME-TYPE TWISTED SUCCESSOR MAP GREEN WITH STRICT NORM DECREASE.
- Outcome B — CYCLIC TWISTED SUCCESSOR STATE GREEN; ONE PRECISE SELF-SIMILARITY BRIDGE REMAINS.
- Outcome C — TWISTED EQUATION GREEN; CANONICAL UNIT/LOCAL DATA NEEDED FOR STATE CLOSURE.
- Outcome D — SMALLER NORM DOES NOT CURRENTLY SUPPORT A CLOSED SUCCESSOR STATE.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSuccessorAudit
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSuccessorAuditApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSuccessorAuditAxiom
    git diff --check

Print axioms for:
- G*Q=a^6;
- each rotated gap equation;
- twisted seventh-power equation;
- any coefficient-class theorem;
- successor-candidate constructor;
- any claimed same-type successor theorem.

Run forbidden-source/import scans on every decisive file.
