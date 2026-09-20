# FLT7TC-005R52 — Eisenstein cube-extraction certificate for the current C=1 branch

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-057.md
- SevenRealCubicSimplestCubicCertificate.lean
- SevenRealCubicSourcePlaneNormSeven.lean
- DkMath/FLT/Three/EisensteinSubstrate.lean
- DkMath/FLT/Three/EisensteinConjugateCoprime.lean
- DkMath/FLT/Three/EisensteinEuclidean.lean
- DkMath/FLT/Three/EisensteinCubeExtraction.lean
- DkMath/FLT/Three/EisensteinUnitSectors.lean

R51 gives, for the current C=1 correction landing x = linearSource a b:

    F(a,b) = -7
    Q(a,b) = 7*q
    P(a,b) = 7*k
    k^2 + 27 = 196*q^3
    7^10 | (3*a + 2*b)

with Q positive definite.

The current high-depth provenance should also force the current Jacobian
parameter k into the calibration residue class:

    k ≡ -13 mod 7^10.

R52 tries to turn this Mordell certificate into an Eisenstein cube extraction
using the already formalized FLT3 Euclidean/UFD layer.

Do not build a generic Mordell or Thue solver.

## Part A — current explicit q and k

For a DirectOrbitTrivialCommonFactorSharpenedPacket P, use the R51
coordinate-transform witnesses A,m and define the corresponding

    a := 2*A - 21*m
    b := -3*A + 28*m
    q := sourcePlaneNormSevenQuadratic a b / 7
    k := sourcePlaneNormSevenJacobian a b / 7

through exact integer equalities rather than integer division where possible.

Prefer explicit polynomial formulas:

    q = A^2 - 19*A*m + 91*m^2

and

    k =
      -13*A^3
      + 357*A^2*m
      - 3234*A*m^2
      + 9653*m^3.

Kernel-check both.

Then prove

    k^2 + 27 = 196*q^3.

Also prove q > 0.

## Part B — high-depth Jacobian orientation

Use:
- 7^9 | m;
- norm-one correction-line equation
  A^3 - 35*A^2*m + 392*A*m^2 - 1421*m^3 = 1;

to prove

    7^10 | (A^3 - 1)

and then

    7^10 | (k + 13).

This is a mandatory current-provenance strengthening.

Do not infer k = -13.

## Part C — parity and the Eisenstein Mordell element

From

    k^2 + 27 = 196*q^3

prove k is odd.

Choose h : Z with

    k = 2*h + 3.

Equivalently h = (k-3)/2, but avoid unsupported integer division.

Define in the FLT3 Eisenstein order:

    z := eisensteinCoord h 3.

Prove

    norm z = 49*q^3.

From 7^10 | k+13 prove

    7^10 | h+8.

## Part D — the norm-seven Eisenstein prime and exact square stripping

Define neutrally

    pi7 := eisensteinCoord 2 1.

Prove

    norm pi7 = 7

and

    pi7^2 = eisensteinCoord 3 5.

Using h ≡ -8 modulo 49, construct integers r,s with

    h = 3*r - 5*s
    3 = 5*r + 8*s.

Equivalently prove

    z = pi7^2 * eisensteinCoord r s.

Preferred explicit formulas, justified by divisibility:

    49*r = 8*h + 15
    49*s = -5*h + 9.

Let

    delta := eisensteinCoord r s.

Prove

    norm delta = q^3.

Also exploit the stronger 7^10 congruence to prove

    7^8 | (r + 1)
    7^8 | (s - 1).

Thus delta is 7-adically close to the unit

    eisensteinCoord (-1) 1 = eisensteinTau^2.

## Part E — q is prime-to-three

Prove from

    k^2 + 27 = 196*q^3

that

    3 ∤ q.

A short 3-adic contradiction is preferred:

1. assume 3 | q;
2. then 3 | k;
3. write k = 3*l;
4. derive 3 | l;
5. compare exact 3-adic depths and contradict the equation.

No valuation framework is required if elementary divisibility is shorter.

## Part F — primitive coordinates of delta

From

    5*r + 8*s = 3

prove

    gcd(|r|,|s|) divides 3.

Combine with 3 ∤ norm delta = q^3 to prove the coordinates are primitive in
the sense needed for conjugate coprimality.

Then prove the neutral theorem

    EisensteinRelPrime delta (conj delta).

Reuse the strategy in EisensteinConjugateCoprime.beta_relPrime_conj:

- a common divisor divides delta - conj delta;
- its norm divides 3*s^2;
- its norm also divides q^3;
- prove the relevant coprimality;
- conclude the divisor norm is 1;
- conclude it is a unit.

Promote this as a reusable neutral lemma if clean.

## Part G — cube extraction

Prove the exact scalar cube identity

    delta * conj delta = (eisensteinCoord q 0)^3.

Apply

    exists_unit_mul_cube_of_coprime_mul_eq_cube

to obtain

    delta = epsilon * gamma^3.

Then use

    exists_sector_mul_cube_of_unit

to absorb the unit cube and normalize to one of the three sectors:

    delta = sector.rep * gamma0^3

where sector is one of

    one, tau, tauSq.

Do not import an FLT3 contradiction theorem.

Only reuse the neutral Euclidean/cube/unit-sector APIs.

## Part H — fixed second-coordinate sector equations

Combine

    z = pi7^2 * delta
    z.snd = 3

with each canonical sector.

Let gamma0 = eisensteinCoord R S.

Use the exact existing formula

    gamma0^3 =
      eisensteinCoord
        (R^3 - 3*R*S^2 - S^3)
        (3*R*S*(R+S)).

Kernel-check the exact cubic equation in each sector.

The three unsigned linear forms before setting equal to 3 are expected to be:

    sector one:
      5*X + 8*Y

    sector tau:
      8*X + 3*Y

    sector tauSq:
      3*X - 5*Y

where
    X = R^3 - 3*R*S^2 - S^3
    Y = 3*R*S*(R+S).

Let Lean determine orientation/sign exactly.

Do not assume numerical reconnaissance.

## Part I — sector elimination audit

Attempt elementary elimination of the sectors.

Useful cheap checks:
- parity;
- mod 3;
- mod 7;
- the inherited congruence
      delta ≡ tau^2 mod 7^8;
- norm gamma0 = q > 0.

The reconnaissance expectation is:
- two canonical sectors may be removable by congruence;
- the surviving sector reduces to a discriminant-2401 cubic equation.

Do not claim this in advance.

If a surviving sector remains a genuine Thue equation, identify its exact
polynomial and inherited high 7-adic congruence.

## Part J — preferred breakthrough

The preferred R52 theorem is:

    norm gamma0 = 1.

Equivalently q = 1.

If q = 1 is proved, then:
- Q(a,b) = 7;
- positive-definite Q gives a finite coordinate shell;
- use norm-seven calibration to classify (a,b) by finite exact arithmetic;
- projectiveLog zero leaves only (2,-3);
- therefore Y = 1;
- contradict correction_ne_one;
- eliminate C=1.

Only add the contradiction if q=1 is kernel-checked.

## Part K — finite shell after q = 1

If q = 1, solve

    a^2 + a*b + b^2 = 7

by an actual finite bound proof.

For example derive |a|,|b| <= 3 from positive-definiteness, then interval_cases
or omega/norm_num.

Intersect with F(a,b) = -7 and recover exactly:

    (-3,1), (1,2), (2,-3).

Use the already checked R50 projective-log calibrations.

This finite search is admissible only after the rigorous Q=7 bound has reduced
the problem to a mathematically finite shell.

## Part L — report boundary honestly

If cube extraction works but one sector remains a genuine discriminant-2401
Thue equation, report that as the exact new frontier.

This is still progress: it replaces the original discriminant-49 norm-minus-
seven classification by one explicitly oriented cube-sector equation carrying
7^8 local data.

## Hard stops

- No generic Mordell/elliptic integral-point solver invented.
- No external Thue classification imported as an axiom.
- No finite unbounded search as completeness.
- No reuse of FLT3 terminal contradiction/descent theorem.
- Neutral FLT3 Eisenstein Euclidean/cube extraction APIs are allowed.
- No p-adic congruence promoted to integer equality.
- No C>1 character work.
- No FLT7 conclusion unless both branches are actually closed.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Deliverables

Primary:
- report-058.md
- ROADMAP.md

Promote reusable neutral Eisenstein bridge lemmas only if clean.

If C=1 closes, add a focused production exclusion module and facade/API/axiom
clients.

## Outcomes

- Outcome A — cube extraction plus sector arithmetic proves q=1 and eliminates
  C=1.
- Outcome B — cube extraction and finite sector reduction are green; one
  explicit sector equation remains.
- Outcome C — exact pi7^2 stripping and conjugate coprimality are green, but
  cube extraction/sector normalization is the frontier.
- Outcome D — the proposed Eisenstein Mordell bridge fails; document the exact
  obstruction.
