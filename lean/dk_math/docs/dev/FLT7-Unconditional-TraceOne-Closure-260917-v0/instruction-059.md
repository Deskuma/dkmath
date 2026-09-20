# FLT7TC-005R53 — Current Eisenstein coprimality and unique tauSq sector

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-058.md
- SevenRealCubicEisensteinCubeCertificate.lean
- SevenRealCubicSimplestCubicCertificate.lean
- SevenRealCubicSourcePlaneNormSeven.lean
- DkMath/FLT/Three/EisensteinSubstrate.lean
- DkMath/FLT/Three/EisensteinConjugateCoprime.lean
- DkMath/FLT/Three/EisensteinCubeExtraction.lean
- DkMath/FLT/Three/EisensteinUnitSectors.lean

R52 established current q/k Mordell data, pi7^2 stripping, delta = eisensteinCoord r s,
norm delta = q^3, 5*r + 8*s = 3, r ≡ -1 mod 7^8, s ≡ 1 mod 7^8,
and neutral cube extraction/sector normalization assuming relative primality.

R53 must first discharge that remaining current-specific relative-primality hypothesis.
Then use the 7-adic residue to force the unique tauSq sector.

## Part A — prove 3 does not divide current q

Neutral target:
  F(a,b) = -7
  Q(a,b) = 7*q
  ----------------
  not (3 | q).

Preferred proof:
1. Assume 3 | q, hence 3 | Q.
2. Modulo 3, Q = a^2 + a*b + b^2 = (a-b)^2, hence a ≡ b mod 3.
3. Write a = b + 3*d.
4. Kernel-check
     F(b+3*d,b) = b^3 + 18*b^2*d + 45*b*d^2 + 27*d^3.
5. Since F = -7, obtain b^3 = 2 mod 9.
6. Prove no cube in ZMod 9 equals 2. A finite by-decide lemma is allowed; native_decide is not.
7. Contradiction.

Promote a clean theorem sourcePlaneNormSeven_three_not_dvd_q.

## Part B — q coprime to the stripped second coordinate

For delta = eisensteinCoord r s with norm delta = q^3, 5*r + 8*s = 3,
and 3 ∤ q, prove the integer coprimality needed downstream between q and s.

Prime-divisor route:
- ell | q and ell | s
- norm delta gives ell | r^2, hence ell | r
- then ell | 5*r + 8*s = 3, so ell = 3
- contradiction.

## Part C — current conjugate relative primality

Prove
  EisensteinRelPrime delta (conj delta)
for current R52 stripping data.

Reuse the FLT3 pattern:
- d divides delta and conj delta => d divides delta - conj delta
- norm d divides 3*s^2
- norm d divides q^3
- Parts A/B give coprimality of q^3 and 3*s^2
- norm d = 1
- d is a unit.

This is the mandatory R53 bridge.

## Part D — current cube extraction packet

Instantiate eisenstein_sector_cube_normalization without any extra relative-primality hypothesis.
Package q,r,s,sector,gamma together with:
- delta = sector.rep * gamma^3
- norm gamma = q
- r ≡ -1 mod 7^8
- s ≡ 1 mod 7^8
- 5*r + 8*s = 3.

Prove norm gamma = q from norm delta = q^3, sector norm 1, q > 0, and norm nonnegativity.

## Part E — force sector = tauSq modulo seven

Use the two evaluations of the Eisenstein order modulo 7 at tau = 3 and tau = 5.
Conceptually:
  ev3(a,b) = a + 3*b
  ev5(a,b) = a + 5*b.

Kernel-check multiplicativity.
For every nonzero x in ZMod 7, x^3 is ±1.

Current delta residue is (-1,1) = tau^2 mod 7, whose evaluations are (2,4).
Show:
- sector one would require cube evaluations (2,4), impossible;
- sector tau would require cube evaluations (3,5), impossible;
- sector tauSq requires cube evaluations (1,1), possible.

Conclude sector = EisensteinUnitSector.tauSq.

## Part F — exact surviving cubic equation

Write gamma = eisensteinCoord R S.
Using sector tauSq and the existing second-coordinate theorem, derive
  3*X - 5*Y = 3
where
  X = R^3 - 3*R*S^2 - S^3
  Y = 3*R*S*(R+S).

Divide exactly by 3 and prove
  R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1.

Define simplestCubicFive if useful and kernel-check its binary-cubic discriminant 2401 = 49^2.
Record that this is Shanks F_5 only as mathematical calibration; do not import any external classification.

## Part G — transport the full 7^8 proximity

Write the current stripping coordinates as
  r = -1 + 8*T
  s =  1 - 5*T
with 7^8 | T.

From delta = tauSq * gamma^3 derive exact cube-coordinate identities
  X = 1 - 5*T
  Y = -3*T.

Hence prove
  T = -R*S*(R+S)
and therefore
  7^8 | R*S*(R+S).

Also prove
  q^3 = 49*T^2 - 13*T + 1.

## Part H — cheap local consequences

Audit exact local consequences of
  F_5(R,S)=1
  7^8 | R*S*(R+S)
  q = R^2 + R*S + S^2 > 0.

At minimum determine possible residues mod 7, q mod 7, and whether exactly one of R,S,R+S
is divisible by 7. State only what Lean proves.

Do not turn Hensel uniqueness into integer equality.

## Part I — attempt q = 1

Preferred breakthrough: q = 1.
Use only kernel-checkable routes:
1. exact F_5 equation plus 7^8 product divisibility;
2. q = norm gamma > 0;
3. existing DkMath/Mathlib reduction or continued-fraction infrastructure if genuinely complete;
4. finite arithmetic only after a proved finite bound.

If q=1 is proved, derive Q(a,b)=7, solve the finite positive-definite shell, use R50 projective-log
calibrations, and eliminate C=1.

## Part J — exact boundary

If q=1 remains open, report precisely the final problem:
  R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1
  7^8 | R*S*(R+S)
  q = R^2 + R*S + S^2 > 0.

## Hard stops

- No external Thue classification as an axiom.
- No FLT3 terminal contradiction or strict descent reuse.
- Neutral FLT3 Euclidean/cube/unit-sector APIs are allowed.
- No finite unbounded search as proof.
- No native_decide.
- No p-adic congruence promoted to integer equality.
- No C>1 character work.
- No FLT7 conclusion unless all branches are actually closed.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Deliverables

- report-059.md
- ROADMAP.md
- promote clean reusable current/neutral theorems
- if C=1 closes, add a focused exclusion module and API/axiom audits.

## Outcomes

- Outcome A — relative primality, unique tauSq sector, and q=1 are kernel-checked; C=1 is eliminated.
- Outcome B — relative primality and unique tauSq sector are green; the high-depth F_5 equation is the precise remaining theorem.
- Outcome C — current relative primality is green but sector uniqueness is the next frontier.
- Outcome D — the proposed relative-primality argument fails; record the exact obstruction.