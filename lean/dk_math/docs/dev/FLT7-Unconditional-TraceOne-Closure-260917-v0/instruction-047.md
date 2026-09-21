# FLT7TC-005R41 — Deep-jet invariant closure and constant-coordinate elimination

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-046.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `SevenRealCubicThetaSeventhPowerMod49.lean`
- `SevenRealCubicThetaCoordinates.lean`
- `SevenRealCubicUnitClass.lean`
- `SevenRealCubicAxisDrop.lean`

R40 stopped at an Outcome E/C boundary after proving the weighted cyclic
trace, the exact trace-plane equation, the calibrated unit
`rho = -alphaUnit^3`, and the neutral linear/square mod-49 seventh-power
jets.

The unrestricted constant-coordinate mod-49 expansion is **not needed**.
The reason is structural: `rho` itself lies on the trace plane, so the scalar
coordinate of the seventh power is annihilated exactly after multiplication
by `rho`.

R41 must close the missing global invariants of the normalized unit `W`,
obtain the exact seventh-power correction `W = rho * v^7`, and use only the
already-green linear/square mod-49 jets to prove the first deeper root
restriction

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0.
```

Do not return to a full constant-coordinate seventh-power expansion.

## Part A — thetaSevenUnit value, norm, and projective class

Reuse

```text
directOrbitDeepJetThetaUnit : SevenRealCubicIntˣ
```

and expose its value:

```text
(directOrbitDeepJetThetaUnit : SevenRealCubicInt) = thetaSevenUnit.
```

Kernel-check the neutral facts needed by R41:

```text
norm thetaSevenUnit = -1
projectiveLog (Additive.ofMul directOrbitDeepJetThetaUnit) = (5,1).
```

A direct coordinate proof is preferred.  With

```text
thetaSevenUnit = -(eisensteinAxisUnitInv^2)
eisensteinAxisUnitInv = <-1,0,1> in the alpha basis,
```

the corresponding theta coordinates are

```text
thetaSevenUnit = -29 - 19*theta - 3*theta^2.
```

This gives the projective class `(5,1)` directly through
`projectiveLog_apply`.

Do not introduce a new Dirichlet-unit theorem for this calculation.

## Part B — signed norm of X

For

```text
X := directOrbitDeepJetXUnit t eta
```

reuse

```text
directOrbitDeepJetXUnit_eq_squareTwistCoeff0_mul_eta_pow14
directOrbit_squareTwist_coeff0_norm_eq_one.
```

Prove

```text
norm (X : SevenRealCubicInt) = 1.
```

The only extra input is that the norm of a model unit is `±1`, hence its
14th power has norm `1`.

Prefer an existing unit-norm/natAbs lemma if available.  A short proof from
multiplicativity with the inverse is acceptable.

## Part C — projective class of X

Prove

```text
projectiveLog (Additive.ofMul X) = (2,4).
```

Use the R27 theorem

```text
directOrbit_squareTwist_coeff_projectiveLog
```

for coefficient zero and rewrite

```text
eta^14 = (eta^2)^7.
```

The seventh-power factor has zero projective log.

## Part D — close the normalized W invariants

For

```text
n := directOrbitDeepJetExponent t = 10 + 14*k
W := directOrbitDeepJetWUnit t eta
```

prove:

```text
Even n
(n : ZMod 7) = 3
norm (W : SevenRealCubicInt) = 1
projectiveLog (Additive.ofMul W) = (1,1).
```

For the norm, the inverse theta-unit contributes

```text
(-1)^n = 1
```

because `n` is even, and Part B gives `norm X = 1`.

For the projective class:

```text
class W
  = -n * (5,1) + (2,4)
  = -3 * (5,1) + (2,4)
  = (1,1) mod 7.
```

Keep the multiplicative-unit and additive-projective-log coercions explicit.

## Part E — exact global seventh-power correction

R40 already proves

```text
projectiveLog rho = (1,1).
```

From Part D obtain

```text
projectiveLog (W * rho⁻¹) = 0.
```

Apply

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

to prove a stable theorem:

```text
exists v : SevenRealCubicIntˣ,
  W = rho * v^7.
```

Normalize exactly to this orientation.

No equality of units may be inferred merely from equal projective logs.

## Part F — define the trace-plane functional

Introduce a small integer-valued helper, preferably local or focused:

```text
def directOrbitTracePlaneForm (x : SevenRealCubicInt) : Int :=
  3 * thetaConstInt x
    - 10 * thetaLinearInt x
    + 35 * thetaSquareInt x
```

or use the displayed expression directly if that keeps the API smaller.

Repackage the existing R40 theorem as

```text
directOrbitTracePlaneForm W = 0.
```

## Part G — eliminate the constant coordinate exactly

Prove the following neutral/specialized multiplication identity for every
`Y : SevenRealCubicInt`:

```text
directOrbitTracePlaneForm
    ((rho : SevenRealCubicInt) * Y)
  = -3 * thetaLinearInt Y + 14 * thetaSquareInt Y.
```

This is the key R41 identity.

A direct coordinate proof is expected.  If

```text
Y = D + E*theta + F*theta^2,
```

then multiplication by

```text
rho = -20 - 13*theta - 2*theta^2
```

gives theta coordinates

```text
const  = -20*D + 14*E - 7*F
linear = -13*D + 8*E
square = -2*D + E + F,
```

and therefore

```text
3*const - 10*linear + 35*square = -3*E + 14*F.
```

Notice that `D` disappears **exactly**.

This theorem replaces the unfinished constant-coordinate mod-49 jet.

## Part H — use only the existing linear/square mod-49 jets

Take the `v` from Part E and set

```text
A := thetaConstInt (v : SevenRealCubicInt)
B := thetaLinearInt (v : SevenRealCubicInt)
C := thetaSquareInt (v : SevenRealCubicInt).
```

First prove

```text
(A : ZMod 7) != 0.
```

Use `thetaConstModSeven_unit_ne_zero` and the literal relationship between
`thetaConstModSeven` and `thetaConstInt`.

Use `theta_coordinate_decomposition` to rewrite the existing neutral theorems

```text
thetaLinear_pow_seven_mod49_neutral A B C
thetaSquare_pow_seven_mod49_neutral A B C
```

for `(v : SevenRealCubicInt)^7`.

Combine them with Part G to prove the focused congruence

```text
49 |
  directOrbitTracePlaneForm
      ((rho : SevenRealCubicInt) * (v : SevenRealCubicInt)^7)
    + 21 * B * A^6.
```

Equivalent sign orientation is acceptable.

Why no constant-coordinate theorem is needed:

- the `thetaConstInt(v^7)` term is annihilated exactly by Part G;
- the square-jet contribution is multiplied by `14`, and its first
  correction is a multiple of `14*7 = 98`, hence already zero modulo `49`;
- only the linear jet leaves the term `-3*(7*B*A^6) = -21*B*A^6`.

Do not re-expand `v^7` directly.

## Part I — force the root linear coordinate

Rewrite Part H using

```text
W = rho * v^7
directOrbitTracePlaneForm W = 0.
```

Deduce

```text
49 | 21 * B * A^6.
```

Then prove

```text
7 | B.
```

A recommended arithmetic route is:

1. cancel one factor `7` from `49 | 3*7*B*A^6`;
2. use primality of `7` and `7 ∤ 3`;
3. use `(A : ZMod 7) != 0` to obtain `7 ∤ A`;
4. conclude `7 | B`.

Expose the stable consequence:

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0.
```

Also expose, if cheap:

```text
exists lambda : ZMod 7,
  projectiveLog (Additive.ofMul v) = (0, lambda).
```

This is the mandatory R41 endpoint.

## Part J — optional Thue normal form

Only after Part I is green, complete the deferred R40 binary-cubic reduction
if it is straightforward.

For

```text
W = A + B*theta + C*theta^2
```

the trace-plane equation has the integral parametrization

```text
A = 5*(r+s)
B = 5*r - 2*s
C = r - s.
```

Substituting into `norm W = 1` gives

```text
r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3 = -1.
```

The class `(1,1)` should imply the mod-seven relation

```text
r = 3*s mod 7
```

or equivalently `7 | r - 3*s`.

Calibration:

```text
r = -3, s = -1
```

corresponds to `rho` and satisfies the equation.

This Part J is optional in R41.  Do not let it block the mandatory deep-jet
root restriction.

## Part K — clash audit

After Part I, audit current checked data only:

1. Does any current theorem force the first projective coordinate of this
   specific `v` to be nonzero?
2. Can `v` be related to the quotient scalarization unit `xi` strongly
   enough to get a second independent coordinate restriction?
3. Does the R27 non-square or mixed-sign theorem constrain the remaining
   second coordinate `lambda`?
4. Does iterating the same trace-plane jet one level deeper force
   `lambda = 0`?

Do not implement the next deep level in R41.

## Hard stops

- Do not restore or require a constant-coordinate mod-49 expansion.
- Do not infer `W = rho` from equal norm, trace, and projective class.
- Do not infer `v = 1` from `thetaLinearModSeven v = 0`.
- Do not call `(0,lambda)` a contradiction.
- Do not import historical terminal/cyclotomic packets as hidden premises.
- No general Thue solver or unbounded search.
- No successor/descent claim.
- No FLT7 contradiction without an independent checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred implementation

Continue in:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean
```

The already-created neutral

```text
SevenRealCubicThetaSeventhPowerMod49.lean
```

should need no constant-coordinate addition.  Modify it only for genuinely
neutral helper lemmas required to reuse its existing two congruences.

Update facade/API/axiom/scratch as needed.

Create `report-047.md` and update `ROADMAP.md`.

## Report questions

1. Was `norm thetaSevenUnit = -1` proved?
2. Was the theta-unit projective class `(5,1)` proved?
3. Were `norm X = 1` and `projectiveLog X = (2,4)` proved?
4. Were `norm W = 1` and `projectiveLog W = (1,1)` proved?
5. Was an exact `W = rho * v^7` obtained?
6. Was the identity
   `Phi(rho*Y) = -3*thetaLinearInt Y + 14*thetaSquareInt Y`
   kernel-checked?
7. Was the constant-coordinate mod-49 theorem avoided entirely?
8. Using only the existing linear/square mod-49 jets, was
   `49 | 21*B*A^6` proved?
9. Was `thetaLinearModSeven v = 0` proved?
10. Did any existing independent invariant contradict this one-dimensional
    projective-root state?

## Outcomes

- Outcome A — the R41 linear-root restriction combines with an existing
  independent invariant to give an actual contradiction.
- Outcome B — all global invariants, exact seventh-power correction, and
  `thetaLinearModSeven v = 0` are green; the remaining root class is
  one-dimensional `(0,lambda)`.
- Outcome C — W norm/class and `W = rho*v^7` are green, but the
  trace-plane/mod-49 transport is the precise frontier.
- Outcome D — W norm is green but its projective class is the precise
  frontier.
- Outcome E — the thetaSevenUnit/X invariant calculations are the precise
  frontier.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetR41Scratch.lean
git diff --check
```

Print axioms for:

- thetaSevenUnit norm/class;
- X norm/class;
- W norm/class;
- exact `W = rho*v^7` theorem;
- `Phi(rho*Y)` constant-elimination theorem;
- mod-49 trace-plane congruence;
- `thetaLinearModSeven v = 0`.

Run forbidden-source/import scans on every decisive file.
