# FLT7TC-005R44 — Square-jet closure and 49th-power correction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-049.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean`
- `SevenRealCubicThetaCoordinates.lean`
- `SevenRealCubicThetaSeventhPowerMod49.lean`
- `SevenRealCubicUnitClass.lean`

R43 is green through Outcome C:

- the same R41 root `v` occurs on the quotient side;
- `Y = thetaU * (v⁻¹)^7`;
- `quotientCore = thetaSevenUnit * Z^7`;
- the quotient-core leading-term remainder has theta depth at least 32;
- the source root is scalar modulo 49 in its two nilpotent theta coordinates.

R44 must finish only the remaining coordinate transport:

```text
source root mod 49 scalar
  -> source sixth power mod 49 scalar
  -> 49 | thetaSquareInt (Z^7)
  -> thetaSquareModSeven Z = 0
  -> thetaSquareModSeven v = 0
  -> projectiveLog v = 0
  -> v = w^7
  -> W = rho * w^49.
```

Do not add a new descent or contradiction unless an already-checked theorem
clashes immediately with the final 49th-power correction.

## Part A — source root differs from its scalar coordinate by 49

For a current root packet `p`, let

```text
A := thetaConstInt p.rho.
```

R43 proves

```text
49 | thetaLinearInt p.rho
49 | thetaSquareInt p.rho.
```

Use `theta_coordinate_decomposition` to prove the model-ring divisibility

```text
(49 : SevenRealCubicInt) |
  p.rho - ofInt A.
```

Prefer an explicit witness built from the quotients of the linear and square
coordinates:

```text
p.rho - ofInt A
  = 49 * (b*theta + c*theta^2).
```

No coordinate injectivity shortcut is needed.

## Part B — source sixth power remains scalar modulo 49

From Part A prove

```text
(49 : SevenRealCubicInt) |
  p.rho^6 - (ofInt A)^6.
```

Use a standard difference-of-powers factorization if convenient, or simply
rewrite

```text
p.rho = ofInt A + 49*q
```

and factor the sixth-power difference structurally.

Then apply the existing scalar-to-coordinate divisibility transport to obtain

```text
(49 : Int) | thetaLinearInt (p.rho^6)
(49 : Int) | thetaSquareInt (p.rho^6).
```

Expose a public theorem, conceptually:

```text
directOrbitPairedDeepJet_source_root_pow_six_mod49_scalar.
```

## Part C — cancel thetaSevenUnit from the depth-32 remainder

Assume the current same-v hypotheses and define

```text
Z := directOrbitPairedDeepJetZ h v.
```

R43 provides

```text
quotientCore = thetaSevenUnit * Z^7
theta^32 | quotientCore - thetaSevenUnit * p.rho^6.
```

Rewrite the second statement as

```text
theta^32 |
  thetaSevenUnit * (Z^7 - p.rho^6).
```

Cancel the unit `thetaSevenUnit` explicitly using
`thetaSevenUnit_isUnit.unit` and its inverse, and prove

```text
theta^32 | Z^7 - p.rho^6.
```

Do not use valuation language.

## Part D — weaken depth 32 to 49

From Part C first obtain

```text
theta^6 | Z^7 - p.rho^6
```

by the obvious power divisibility.

Apply the existing R42 helper

```text
directOrbit_axis_pow_six_dvd_imp_natCast49
```

to prove

```text
(49 : SevenRealCubicInt) | Z^7 - p.rho^6.
```

Transport to theta coordinates:

```text
49 |
  thetaSquareInt (Z^7) - thetaSquareInt (p.rho^6).
```

If the existing scalar-coordinate transport only handles `49 | x`, apply it
to the difference and use additivity of `thetaSquareInt`.

Combine with Part B to prove the stable endpoint

```text
49 | thetaSquareInt (Z^7).
```

Optionally expose the same linear-coordinate divisibility if it is free, but
it is not needed for R44.

## Part E — prove the scalar V is nonzero modulo seven

Use the current C=1 scalarization

```text
quotientSquareRoot = xi * (V : SevenRealCubicInt)
```

and

```text
directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd
```

to prove

```text
¬ 7 | V.
```

A direct contradiction is preferred:

if `V = 7*m`, then

```text
(V : SevenRealCubicInt)
  = theta^3 * thetaSevenUnit * m,
```

so `theta | (V : SevenRealCubicInt)`; multiplying by the unit `xi`
would make theta divide the quotient square root.

Do not call `V` a global unit.

## Part F — theta-local unit data for Z

Recall

```text
Z = (v⁻¹ : SevenRealCubicInt) * (V : SevenRealCubicInt)^2.
```

Prove:

```text
(thetaConstInt Z : ZMod 7) != 0
thetaLinearModSeven Z = 0.
```

For the constant coordinate:

- `thetaConstModSeven (v⁻¹) != 0` because `v⁻¹` is a global unit;
- `7 ∤ V` from Part E gives `(V : ZMod 7) != 0`;
- the scalar `V^2` has theta constant `V^2` and zero nilpotent coordinates.

For the linear coordinate, first derive

```text
thetaLinearModSeven (v⁻¹ : SevenRealCubicInt) = 0
```

from

```text
thetaLinearModSeven v = 0
v * v⁻¹ = 1
```

and `thetaLinearModSeven_mul`.

Then scalar multiplication by `V^2` preserves zero linear coordinate.

## Part G — square seventh-power jet on Z

Let

```text
AZ := thetaConstInt Z
BZ := thetaLinearInt Z
CZ := thetaSquareInt Z.
```

Use `theta_coordinate_decomposition Z` to instantiate

```text
thetaSquare_pow_seven_mod49_neutral AZ BZ CZ.
```

Together with Part D, prove

```text
49 |
  7 * (CZ * AZ^6 + 3 * BZ^2 * AZ^5).
```

Cancel one factor seven:

```text
7 |
  CZ * AZ^6 + 3 * BZ^2 * AZ^5.
```

Reduce in `ZMod 7`.

Part F gives

```text
AZ != 0
BZ = 0.
```

Therefore prove

```text
(CZ : ZMod 7) = 0
```

and expose the mandatory new theorem

```text
thetaSquareModSeven Z = 0.
```

This is the central R44 calculation.

## Part H — transport the square coordinate from Z to v inverse

Use

```text
Z = (v⁻¹) * V^2
```

and `thetaSquareModSeven_mul`.

The scalar `V^2` has

```text
thetaLinearModSeven = 0
thetaSquareModSeven = 0
thetaConstModSeven != 0.
```

Together with

```text
thetaLinearModSeven (v⁻¹) = 0
thetaSquareModSeven Z = 0
```

deduce

```text
thetaSquareModSeven (v⁻¹ : SevenRealCubicInt) = 0.
```

The only cancellation needed is by the nonzero scalar residue of `V^2`.

## Part I — transport from v inverse back to v

Use

```text
v * v⁻¹ = 1
```

and `thetaSquareModSeven_mul`.

At this point both linear coordinates are zero:

```text
thetaLinearModSeven v = 0
thetaLinearModSeven v⁻¹ = 0.
```

Part H gives the inverse square coordinate zero.  Hence

```text
0 =
  thetaSquareModSeven (v * v⁻¹)
  = thetaSquareModSeven v *
      thetaConstModSeven v⁻¹.
```

Since the constant coordinate of a unit is nonzero, conclude

```text
thetaSquareModSeven (v : SevenRealCubicInt) = 0.
```

Expose this as a public same-v theorem.

## Part J — projective-log closure

Combine the existing R41 endpoint

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0
```

with Part I.

Prove directly from `projectiveLog_apply` that

```text
projectiveLog (Additive.ofMul v) = 0.
```

Be explicit about:

```text
unitNilpotentX v = 0
unitNilpotentY v = 0
```

using the nonzero constant coordinate of the unit.

Then apply

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

to get

```text
exists w : SevenRealCubicIntˣ, v = w^7.
```

Do not conclude `v = 1`.

## Part K — expose the 49th-power correction

Starting from the exact R41 equality

```text
W = rho0 * v^7
```

and Part J

```text
v = w^7,
```

prove

```text
W = rho0 * w^49.
```

Use the literal exponent identity `7*7 = 49`.

Prefer a provenance-preserving wrapper for the current C=1 packet returning
`eta, xi, v, w` and the relevant equations.

Mandatory wrapper conclusions should include at least:

```text
W = rho0 * v^7
thetaLinearModSeven v = 0
thetaSquareModSeven v = 0
projectiveLog v = 0
v = w^7
W = rho0 * w^49
quotientCore = thetaSevenUnit * Z^7.
```

## Part L — clash audit

After Part K is green, audit only existing checked theorems.

1. Expand
   `X = thetaU^n * W`
   and
   `X = directOrbitSquareTwistCoeff0 * eta^14`.
   Does `W = rho0*w^49` force
   `directOrbitSquareTwistCoeff0` to be a square, contradicting
   `directOrbit_squareTwist_coeff0_not_square`?
2. If not, determine the exact residual parity/unit obstruction that prevents
   the square conclusion.
3. Compare the real embedding signs of
   `rho0 * w^49` with the existing mixed-sign theorem for coefficient zero.
   Is the sign pattern already incompatible, or can `w` absorb it?
4. Does the 49th-power correction make the optional binary cubic/Thue surface
   finite or rigid using only existing repository lemmas?

Do not start a new general Thue solver, Baker theory, or unit-equation theory
in R44.

## Hard stops

- Do not infer a contradiction merely from `v = w^7`.
- Do not infer `w = 1`.
- Do not call `V` a global algebraic unit.
- No hidden historical terminal/cyclotomic contradiction imports.
- No well-founded descent claim.
- No arbitrary mod-343 seventh-power expansion.
- No FLT7 closure without an independent checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred implementation

Continue in

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean
```

unless heartbeat/file-size pressure clearly justifies a continuation module.

Neutral helpers may be factored out only when truly packet-independent.

Update:

- `DkMath.FLT.Seven` facade if needed;
- focused API check;
- focused axiom audit;
- `R44Scratch`;
- `report-050.md`;
- `ROADMAP.md`.

## Report questions

1. Was `49 | p.rho - ofInt(thetaConstInt p.rho)` proved in the model ring?
2. Were the linear/square coordinates of `p.rho^6` proved divisible by 49?
3. Was thetaSevenUnit cancelled from the depth-32 quotient remainder?
4. Was `49 | thetaSquareInt (Z^7)` proved?
5. Was `7 ∤ V` proved from the quotient-square-root axis exclusion?
6. Were `thetaConst(Z) != 0` and `thetaLinearModSeven Z = 0` proved?
7. Did the neutral mod-49 square jet force
   `thetaSquareModSeven Z = 0`?
8. Was this transported first to `v⁻¹`, then to
   `thetaSquareModSeven v = 0`?
9. Was `projectiveLog v = 0` kernel-checked?
10. Was `v = w^7` kernel-checked?
11. Was `W = rho0*w^49` exposed?
12. Did an existing independent theorem produce an actual contradiction?

## Outcomes

- Outcome A — the 49th-power correction clashes with an existing independent
  invariant and gives an actual contradiction.
- Outcome B — square-jet/projective-root closure is fully green:
  `projectiveLog v = 0`, `v = w^7`, and `W = rho0*w^49`; no
  contradiction yet.
- Outcome C — `49 | thetaSquareInt(Z^7)` is green, but the mod-seven
  square-coordinate extraction/transport is the precise frontier.
- Outcome D — source sixth-power scalarity is green, but quotient remainder
  transport to `49 | thetaSquareInt(Z^7)` is the precise frontier.
- Outcome E — source sixth-power scalarity itself is the precise frontier.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR44Scratch.lean
git diff --check
```

Print axioms for:

- source sixth-power mod-49 scalarity;
- cancelled quotient remainder;
- `49 | thetaSquareInt(Z^7)`;
- `thetaSquareModSeven Z = 0`;
- `thetaSquareModSeven v = 0`;
- `projectiveLog v = 0`;
- `v = w^7`;
- `W = rho0*w^49`.

Run forbidden-source/import scans on all decisive files.
