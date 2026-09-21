# FLT7TC-005R57 — Thomas F5 internal SevenRealCubic bridge

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative project inputs:

- report-062.md
- ThomasThueSixApproximation.lean
- ThomasThueSixAudit.lean
- SevenRealCubicHighDepthFive.lean
- SevenRealCubicThetaCoordinates.lean
- SevenRealCubicThetaSeventhPowerDepth.lean
- SevenRealCubicUnitClass.lean
- SevenRealCubicEisenstein.lean
- SevenRealCubicInt.lean

R56 completed the fixed n=6 approximation-to-convergent bridge but the
published finite denominator bound remains unavailable.

R57 investigates a completely internal route discovered from the existing
conductor-7 cubic model.

Key exact observation to kernel-check:

    lambda := alpha^2 + alpha - 1

satisfies the Thomas polynomial

    lambda^3 - 5*lambda^2 - 8*lambda - 1 = 0.

Hence

    F5(R,S) = norm (R - lambda*S).

Moreover, in theta = alpha - 3 coordinates,

    lambda = 11 + 7*theta + theta^2.

Thus on a cyclically normalized deep-S branch, 7^8 | S implies the norm-one
Thomas unit

    u := R - lambda*S

has theta nilpotent depth 8.

The goal is to reconnect the Thomas frontier to the already formalized
SevenRealCubic unit/depth machinery and determine whether this yields a new
closure mechanism.

Do not assume it yields a contradiction.

## Part A — Thomas root inside SevenRealCubic

Create a focused neutral module, preferred:

    DkMath/FLT/Seven/SevenRealCubicThomasUnit.lean

Define

    thomasLambda : SevenRealCubicInt :=
      alpha^2 + alpha - 1.

Prove:

    thomasLambda = ⟨-1,1,1⟩

and

    thomasLambda^3
      - 5*thomasLambda^2
      - 8*thomasLambda
      - 1 = 0.

Also prove:

    norm thomasLambda = 1.

Construct

    thomasLambdaUnit : SevenRealCubicIntˣ.

Do not use the real-root approximation module for these proofs.

## Part B — theta coordinates and unit class of lambda

Prove exactly:

    thomasLambda
      = ofThetaCoordinates 11 7 1

so

    thetaConstInt thomasLambda = 11
    thetaLinearInt thomasLambda = 7
    thetaSquareInt thomasLambda = 1.

Kernel-check the projective class:

    projectiveLog (Additive.ofMul thomasLambdaUnit) = (0,2)

with the exact ZMod 7 value determined by Lean.

Also prove the useful exact unit relation:

    thomasLambda^2 * (1 + alpha) = alpha^6.

Lift it to units if clean.

Record this as an index-two style relation only.
Do NOT infer from it that alpha and 1+alpha form a fundamental unit basis.

## Part C — F5 is the norm form of the Thomas plane

For all R S : Z prove:

    norm ((R : SevenRealCubicInt) - thomasLambda * S)
      = F5 R S.

Preferred proof:

- direct coordinate/norm expansion, or
- conjugate-product identity if shorter.

Define, if useful,

    thomasPlaneElement R S :=
      (R : SevenRealCubicInt) - thomasLambda * S.

Prove its theta coordinates:

    thetaConstInt  = R - 11*S
    thetaLinearInt = -7*S
    thetaSquareInt = -S.

Thus its plane equation is exactly

    thetaLinearInt x = 7 * thetaSquareInt x.

This is a different plane from IsSourcePlane; name it separately if exposed.

## Part D — norm-one unit lift from F5=1

Prove a neutral theorem:

    F5 R S = 1
      -> IsUnit (thomasPlaneElement R S).

Construct a unit lift with exact value and norm one.

Avoid duplicating a generic norm-one-is-unit theorem if an existing public
one can be reused; if the needed theorem is currently private, promote the
smallest neutral version rather than copy proof bodies.

## Part E — inverse preserves theta nilpotent depth

Add the reusable theorem:

    theorem thetaNilpotentDepth_inv
        (u : SevenRealCubicIntˣ) (n : Nat)
        (h : ThetaNilpotentDepth n (u : SevenRealCubicInt)) :
        ThetaNilpotentDepth n
          ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)

or an equivalent iff.

Preferred direct proof in theta coordinates.

If

    u = A + B*theta + C*theta^2
    u⁻¹ = D + E*theta + F*theta^2

use theta^3 = -7*theta^2 -14*theta -7 and theta^4 =
35*theta^2 +91*theta +49 to obtain the exact product coordinates.

From u*u⁻¹=1:

    0 = A*E + B*D -14*(B*F + C*E) + 91*C*F

and after E is controlled,

    0 = A*F + B*E + C*D -7*(B*F + C*E) + 35*C*F.

All terms except A*E / A*F are divisible by 7^n.

Use that a unit has thetaConst mod 7 nonzero, hence A is coprime to 7^n.

Handle n=0 separately if convenient.

This theorem is mandatory if it is technically reasonable.

## Part F — cyclic normalization to deep S

R54 gives exactly one deep factor among

    R, S, R+S

and sigma5(R,S)=(-R-S,R) preserves F5, Q5, T5.

Package a neutral normalization theorem:

    F5 R S = 1
    7^8 | R*S*(R+S)
      -> exists R' S',
           F5 R' S' = 1
         and Q5 R' S' = Q5 R S
         and T5 R' S' = T5 R S
         and 7^8 | S'
         and 7 ∤ R'.

Use only identity / sigma5 / sigma5^2.

Retain an exact relation back to the source pair.

## Part G — current Thomas unit has depth eight

For a normalized deep-S solution define

    u := thomasPlaneElement R S.

From

    7^8 | S

and Part C prove

    ThetaNilpotentDepth 8 u.

From F5=1 construct the unit lift U and prove

    ThetaNilpotentDepth 8 (U : SevenRealCubicInt).

Then Part E gives the same depth for U⁻¹.

Apply the existing theorem

    unit_is_pow_seven_pow_of_inverse_depth U 8

to obtain

    exists t : SevenRealCubicIntˣ,
      U = t^(7^8).

This is the mandatory current endpoint.

Also record:

    projectiveLog U = 0.

## Part H — exact seventh-root Thomas-plane return equation

Audit whether U = t^7 with U in the Thomas plane gives a reusable exact
equation on t.

The plane condition is

    thetaLinearInt (t^7)
      = 7 * thetaSquareInt (t^7).

Using existing exact seventh-power quotient formulas derive

    seventhThetaLinearQuotient A B C
      = 7 * seventhThetaSquareQuotient A B C.

Reduce modulo 7 and recover the expected first depth condition B ≡ 0 mod 7.

Determine whether the exact equation factors after B=7*b1 in a way that
recovers the same Thomas plane, a smaller parameter pair, or a strict descent.

Do not claim such a descent unless an exact integer successor is constructed.

## Part I — compare with the R45 finite-Hensel mechanism

Document the structural comparison:

R45:
    source depth -> repeated seventh-root extraction -> finite endpoint.

R57:
    Thomas high-depth plane -> repeated seventh-root extraction.

Determine whether R57 merely restates the already known 7^8 depth, or whether
the extra exact Thomas-plane equation supplies information that R45 did not
have.

This distinction is essential.

## Part J — external Thomas bound remains a parallel fallback

Do not delete or weaken R56.

If the internal route yields no new clash, the exact external boundary remains:

    FixedThomasSixBound:
      F5(R,S)=1 -> |S| < 5764801

or an equivalent finite continued-fraction certificate.

Record both routes separately in the report.

## Part K — closure only if genuinely obtained

If the internal route unexpectedly proves

    R*S*(R+S)=0

or q=1, consume the already checked R54 shell and trace back to eliminate the
C=1 sharpened packet.

Otherwise stop at the exact new unit/depth endpoint.

## Hard stops

- No assumption that alpha and 1+alpha are a full fundamental unit basis.
- No inference from lambda^2*(1+alpha)=alpha^6 to a global unit classification.
- No infinite Hensel/descent claim without a well-founded successor.
- No external Thomas/Mignotte theorem as axiom.
- No p-adic equality promoted from congruence.
- No C>1 work in R57.
- No FLT7 final theorem.
- No sorry, sorryAx, admit, unsafe, native_decide, or project axiom.

## Deliverables

Primary:

- SevenRealCubicThomasUnit.lean if Parts A-G are clean;
- report-063.md;
- ROADMAP.md.

Add focused API/axiom tests for promoted production theorems.

## Outcomes

- Outcome A — internal Thomas-unit route gives a genuine strict successor or
  contradiction and eliminates C=1.
- Outcome B — F5 norm identification, inverse-depth preservation, cyclic
  normalization, and U=t^(7^8) are kernel-checked; exact return equation is the
  new frontier.
- Outcome C — F5 norm identification/depth bridge is green but inverse-depth
  or unit-power extraction needs additional infrastructure.
- Outcome D — the internal route is provably only a reformulation of R54/R56;
  keep the external fixed-n=6 certificate as the true frontier.
