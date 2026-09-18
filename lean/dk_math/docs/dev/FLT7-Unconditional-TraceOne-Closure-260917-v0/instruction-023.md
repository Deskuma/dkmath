# FLT7TC-005R18 — Productionize Astra-001 orbit split and strict smaller norm

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Source of truth:

- astra-report-001.md
- astra-001/OrbitChecks.lean
- astra-001-findings-freeze.md

This checkpoint productionizes the surviving Astra-001 route.
Do not attempt successor-state reconstruction yet.

## Goal

Starting from the current DirectRealCubicRootPacket, kernel-check in production:

1. exact theta depths of the first orbit gap and homogeneous seventh quotient;
2. theta-stripped coprime cores;
3. associated seventh-power extraction of both cores with explicit units;
4. the exact extracted unit classes;
5. the strict positive norm reduction

       0 < Int.natAbs (norm g) < a <= gapRoot,

   where gapRoot = 7^k * a and 7 ∤ a.

Stop there. This is a smaller-norm theorem, not yet a descent theorem.

## Part A — normalize the gap root

For A = r.summit.gapRoot define

    k := padicValNat 7 A

and obtain a positive seven-unit part a with

    A = 7^k * a
    0 < a
    ¬ 7 ∣ a.

Reuse existing valuation/decomposition APIs where possible.

Keep the equality orientation convenient for the later theta-depth calculation.

## Part B — direct orbit gap and quotient

For p : DirectRealCubicRootPacket source r define

    rho0 := p.rho
    rho1 := rotateEquiv p.rho
    d := rho1 - rho0
    H := seventhQuotient rho1 rho0

using the existing FLT7 homogeneous seventh quotient definition.

Reuse R17/Astra facts to prove:

    d * H
      = orbitUnit01 *
        (eisensteinAxis^5 * thetaSevenUnit * A^2)^7.

Do not reconstruct this from historical packets.

## Part C — exact theta depths

Productionize the Astra deductions:

    HasExactThetaDepth H 3

and

    HasExactThetaDepth d (32 + 42*k).

The first should reuse the generic theorem already present in
SevenRealCubicAxisDrop when possible.

For the second, combine:

- exact total depth of d*H from the explicit edge factorization;
- depth 3 of H;
- 7 = theta^3 * thetaSevenUnit;
- A = 7^k*a with a theta-unit.

Do not infer exact depth from divisibility alone.

Also expose the weaker stable corollary:

    eisensteinAxis^32 ∣ d.

## Part D — strip theta exactly

Construct d0,h0 with

    d = theta^(32+42*k) * d0
    H = theta^3 * h0
    theta ∤ d0
    theta ∤ h0.

Package these witnesses.

## Part E — current-provenance coprimality

Productionize the scratch proof that rho0 and rho1 are coprime.

The proof must use:

- the edge seventh-power factorization;
- theta-unit property of the roots;
- gcd(A,B)=1 via the mapped integer Bezout relation;
- rho0*rho1*rho2 = B or the checked equivalent norm identity.

Do not infer this from norms alone.

Then prove the generic-to-current common-prime statement:

    any prime dividing both d and H is associated to theta.

After stripping exact theta powers, conclude:

    IsCoprime d0 h0.

No historical routing/receiver packet may be assumed.

## Part F — coprime seventh-power extraction

From the stripped product equation derive exactly:

    d0 * h0
      = orbitUnit01 * (thetaSevenUnit^(1+2*k) * a^2)^7

up to the repository's preferred unit orientation.

Use the existing generic power-factor/PID machinery rather than copying it.

Construct witnesses

    eta nu : SevenRealCubicIntˣ
    g h : SevenRealCubicInt

such that

    d0 = (eta : SevenRealCubicInt) * g^7
    h0 = (nu : SevenRealCubicInt) * h^7.

Prove the unit classes:

    projectiveLog eta = (2,4)
    projectiveLog nu = (5,1).

If the precise unit representatives differ by a seventh power, state the class
equalities rather than forcing literal unit equality.

## Part G — total positivity and real inequalities

Productionize only the exact amount required by the norm bound.

Show that rho is totally positive under all three real embeddings, using its
origin as the relative norm of gammaNorm and the already checked CM
conjugation transport.

Do not introduce a broad positivity framework if a direct three-embedding
proof is shorter.

Productionize the two Astra inequalities:

For nonnegative real s,t:

    H7(s,t) >= 7*(s*t)^3.

For real L,R with D=L-R:

    64*H7(L,R) >= D^6.

The p=7 versions are sufficient here.

## Part H — strict smaller norm

Let

    G := Int.natAbs (SevenRealCubicInt.norm g).

Prove:

    0 < G
    G < a
    a <= A.

The proof should follow Astra-001:

1. Norm(H) >= 7^3 * B^6 from total positivity and the first inequality.
2. Taking absolute norms of the stripped gap equation yields

       G^7 * B^6 <= a^42.

3. From the original endpoint equation and the second inequality derive

       B^7 >= 7^35 * A^42 / 64
       and in particular B^6 > a^35.

4. If G >= a, obtain

       G^7 * B^6 > a^42,

   contradiction.

Avoid informal real/integer coercion gaps; isolate them in small lemmas.

## Part I — stable packet

Create a production packet retaining all data needed by a future successor
constructor, conceptually:

    structure DirectOrbitSmallerNormPacket ... where
      k : Nat
      a : Nat
      ...
      g : SevenRealCubicInt
      eta : SevenRealCubicIntˣ
      gapCore_eq : ...
      g_norm_pos : 0 < natAbs (norm g)
      g_norm_lt_unitPart : natAbs (norm g) < a
      unitPart_le_gapRoot : a <= gapRoot

Do NOT define a successor counterexample or claim a descent.

## Hard stops

- No CubicGapSeventhShapeReceiver.
- No RamifiedSignedRootRoutingPacket as an input.
- No successor state assumption.
- No claim of infinite descent.
- No inference of element coprimality from rational norms.
- No dropping eta/nu units.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitSplit.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitSplitApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitSplitAxiom.lean

Create report-023.md and update ROADMAP.md.

## Outcome labels

- Outcome A — DIRECT ORBIT SPLIT GREEN; STRICT SMALLER NORM PROVED IN PRODUCTION.
- Outcome B — EXACT DEPTH/COPRIME SPLIT GREEN; ARCHIMEDEAN SMALLER-NORM BOUND REMAINS.
- Outcome C — EXACT DEPTH GREEN; STRIPPED CURRENT-PROVENANCE COPRIMALITY IS THE FRONTIER.
- Outcome D — ASTRA SCRATCH CLAIM FAILS TO TRANSPORT TO PRODUCTION.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitSplit
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitSplitApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitSplitAxiom
    git diff --check

Print axioms for:

- exact depth of d;
- exact depth of H;
- stripped-core coprimality;
- extracted seventh-power roots;
- total positivity input used in the bound;
- strict smaller norm theorem.

Run forbidden-source scans on every decisive file.
