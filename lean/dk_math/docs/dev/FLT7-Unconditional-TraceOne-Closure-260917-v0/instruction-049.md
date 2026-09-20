# FLT7TC-005R43 — Paired deep-jet transport and projective-root closure

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-048.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean`
- `PrimeTraceOneDirectRealCubicLocalClass.lean`
- `PrimeTraceOneDirectRealCubicOrbitSplit.lean`
- `SevenRealCubicThetaCoordinates.lean`
- `SevenRealCubicThetaSeventhPowerMod49.lean`

R42 implemented the exact paired algebra/core layer:

- the quotient unit model `Y`;
- the literal fixed-unit identity;
- exact gap/quotient scalarized core formulas;
- exact `X * Y` paired product;
- a depth-32 canonical quotient witness with `theta^31 | d`;
- neutral `theta^6 -> 49` and `theta^9 -> 343` divisibility helpers.

R43 must connect these existing pieces.  No new global theory is needed.

The target is to prove, for the same R41 seventh-root unit `v`,

```text
thetaSquareModSeven (v : SevenRealCubicInt) = 0
projectiveLog (Additive.ofMul v) = 0
exists w : SevenRealCubicIntˣ, v = w^7.
```

Equivalently, the R41 correction strengthens from

```text
W = rho * v^7
```

to

```text
W = rho * w^49.
```

This is still not by itself an FLT7 contradiction.

## Part A — recover the same v on the quotient side

Let

```text
t := h.squareRefinement
k := t.powerSplit.gapSplit.k
n := directOrbitDeepJetExponent t = 10 + 14*k
X := directOrbitDeepJetXUnit t eta
Y := directOrbitPairedDeepJetY h xi
thetaU := directOrbitDeepJetThetaUnit
rho0 := directOrbitDeepJetRho.
```

Assume the R41 exact correction

```text
directOrbitDeepJetWUnit t eta = rho0 * v^7.
```

Use

```text
directOrbitDeepJetWUnit t eta = thetaU⁻¹^n * X
directOrbitPairedDeepJet_cores_product_unit_eq
directOrbitPairedDeepJet_fixed_unit_identity
```

to prove the literal unit identity

```text
Y = thetaU * (v⁻¹)^7.
```

The exponent arithmetic is

```text
7*(1 + 2*k) - (10 + 14*k) = -3.
```

Do not introduce a fresh seventh root.  The theorem must use the exact same
`v` supplied by R41.

A direct group calculation is preferred after rewriting

```text
X = thetaU^n * rho0 * v^7.
```

## Part B — exact quotientCore seventh-power form

Combine Part A with the existing quotient scalarization

```text
quotientCore = Y * V^14.
```

Define

```text
def directOrbitPairedDeepJetZ
    (h ...) (v : SevenRealCubicIntˣ) : SevenRealCubicInt :=
  (v⁻¹ : SevenRealCubicInt) * (h.v : SevenRealCubicInt)^2
```

and prove

```text
quotientCore =
  thetaSevenUnit * (directOrbitPairedDeepJetZ h v)^7.
```

Use `V^14 = (V^2)^7` literally.

## Part C — expose the actual depth-32 quotient remainder

R42 gives

```text
exists d,
  theta^31 | d
  and quotientCore = directOrbitQuotientCoreCanonical p d.
```

From the explicit canonical expansion, prove

```text
theta^32 |
  quotientCore - thetaSevenUnit * p.rho^6.
```

Every non-leading term must be checked individually or by a small helper:

- first remainder term contains `theta*d`;
- `theta^31 | d`;
- all later terms contain at least as much theta depth.

Do not weaken to theta^3 before proving this theorem.

Prefer the public theorem shape

```text
theorem directOrbitPairedDeepJet_quotientCore_sub_leading_axis_pow32_dvd ...
```

## Part D — exact rotation-gap theta coordinates

Prove neutral formulas for arbitrary theta coordinates:

if

```text
r0 = ofThetaCoordinates A B C
```

then

```text
thetaConstInt  (rotateEquiv r0 - r0) = -7*C
thetaLinearInt (rotateEquiv r0 - r0) = 3*B - 21*C
thetaSquareInt (rotateEquiv r0 - r0) = B - 6*C.
```

These are exact integer equalities.

A direct proof from `rotateEquiv`, `rotateHom`, and
`ofThetaCoordinates` is expected.

Package them as one conjunction theorem if convenient.

## Part E — scalar divisibility transports to theta coordinates

Add neutral helpers:

```text
(n : SevenRealCubicInt) | x
  -> n | thetaConstInt x

(n : SevenRealCubicInt) | x
  -> n | thetaLinearInt x

(n : SevenRealCubicInt) | x
  -> n | thetaSquareInt x
```

for integer scalars `n : Int` or specialized to `49,343`.

The proof should use multiplication by a scalar in the theta basis, not any
unproved injectivity shortcut.

Then, from

```text
theta^32 | directOrbitGap p
```

weaken to `theta^9`, apply R42's `theta^9 -> 343`, and use Part D to prove

```text
49 | thetaLinearInt p.rho
49 | thetaSquareInt p.rho.
```

Suggested arithmetic:

1. `343 | -7*C` gives `49 | C`;
2. `343 | B - 6*C` gives `49 | B - 6*C`;
3. combine with `49 | C` to get `49 | B`.

Expose a stable theorem saying the source root is scalar modulo 49 in its two
nilpotent theta coordinates.

## Part F — sixth power of the source remains scalar modulo 49

Let

```text
A := thetaConstInt p.rho.
```

From Part E prove

```text
(49 : SevenRealCubicInt) |
  p.rho - ofInt A.
```

Then use the difference-of-powers factorization to obtain

```text
(49 : SevenRealCubicInt) |
  p.rho^6 - (ofInt A)^6.
```

Conclude

```text
49 | thetaLinearInt (p.rho^6)
49 | thetaSquareInt (p.rho^6).
```

Prefer this structural proof over a full sixth-power coordinate expansion.

## Part G — compare the quotient seventh power to the source sixth power

Combine Parts B and C:

```text
theta^32 |
  thetaSevenUnit *
    (Z^7 - p.rho^6).
```

Cancel the unit `thetaSevenUnit` in divisibility and obtain

```text
theta^32 | Z^7 - p.rho^6.
```

Weaken to `theta^6`, apply

```text
directOrbit_axis_pow_six_dvd_imp_natCast49
```

and prove

```text
(49 : SevenRealCubicInt) | Z^7 - p.rho^6.
```

Using Part F and coordinate transport, conclude

```text
49 | thetaSquareInt (Z^7).
```

Expose this theorem publicly.

## Part H — prove V is a theta-local unit

Use

```text
directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd
quotientSquareRoot = xi * V
```

to prove

```text
¬ 7 ∣ h.v.
```

Reason: if `7 | V`, then from
`7 = theta^3 * thetaSevenUnit` we get `theta | (V : O)`, hence theta
divides `xi * V = quotientSquareRoot`, contradiction.

Do not call `V` a global algebraic unit.

Then prove for

```text
Z = (v⁻¹) * V^2
```

that

```text
(thetaConstInt Z : ZMod 7) ≠ 0.
```

Use:

- the nonzero theta constant of the global unit `v⁻¹`;
- `7 ∤ V`;
- the scalar multiplication formula.

## Part I — transport the R41 linear restriction to Z

R41 gives

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0.
```

First prove the inverse consequence

```text
thetaLinearModSeven (v⁻¹ : SevenRealCubicInt) = 0
```

from `v * v⁻¹ = 1` and the multiplication law.

Since `V^2` is scalar, conclude

```text
thetaLinearModSeven Z = 0.
```

## Part J — use the neutral mod-49 square jet

Write

```text
A := thetaConstInt Z
B := thetaLinearInt Z
C := thetaSquareInt Z.
```

Use

```text
thetaSquare_pow_seven_mod49_neutral A B C
```

together with Part G to prove

```text
49 | 7 * (C*A^6 + 3*B^2*A^5).
```

Cancel one factor seven to obtain

```text
7 | C*A^6 + 3*B^2*A^5.
```

Reduce modulo seven.

By Parts H and I,

```text
A != 0 mod 7
B = 0 mod 7.
```

Therefore prove

```text
C = 0 mod 7
```

and expose

```text
thetaSquareModSeven Z = 0.
```

This is the mandatory new local conclusion of R43.

## Part K — transport the square restriction back to v

Use

```text
Z = (v⁻¹) * V^2
```

and the theta-square multiplication formula.

Because the scalar `V^2` has:

```text
thetaLinearModSeven = 0
thetaSquareModSeven = 0
thetaConstModSeven != 0,
```

Part J implies

```text
thetaSquareModSeven (v⁻¹ : SevenRealCubicInt) = 0.
```

Then use `v * v⁻¹ = 1`, together with both linear coordinates zero, to prove

```text
thetaSquareModSeven (v : SevenRealCubicInt) = 0.
```

Expose this theorem for the same R41 root `v`.

## Part L — close the projective root class

From R41 and Part K prove

```text
projectiveLog (Additive.ofMul v) = 0.
```

Do not merely say the first and second raw coordinates vanish; check the
definition of `projectiveLog`.  Since the normalized linear coordinate is
zero, the quadratic correction term vanishes as well.

Apply

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

to obtain

```text
exists w : SevenRealCubicIntˣ, v = w^7.
```

Combine with R41:

```text
W = rho0 * v^7
```

to expose, if cheap,

```text
W = rho0 * w^49.
```

This is the mandatory R43 endpoint.

## Part M — provenance-preserving wrapper

Provide a theorem or small packet that starts only from the current canonical
`C = 1` packet and its two scalarizing units `eta, xi`, then returns
`v,w` with at least:

```text
W = rho0 * v^7
thetaLinearModSeven v = 0
thetaSquareModSeven v = 0
projectiveLog v = 0
v = w^7
W = rho0 * w^49
quotientCore = thetaSevenUnit * ((v⁻¹)*V^2)^7.
```

Do not duplicate unrelated fields.

## Part N — clash audit only

After Part L/M is green, inspect current checked data.

Questions:

1. Does `W = rho0 * w^49` force the square-twist coefficient zero to be a
   square, contradicting R27?
2. Does its norm-one mixed-sign theorem exclude the resulting 49th-power
   correction?
3. Does the exact fixed unit `rho0 = -alpha^3` leave a sign obstruction at
   any real embedding?
4. Can the paired-core mechanism be iterated to force arbitrarily high
   seventh-power divisibility of the same unit correction?
5. Does the optional Thue equation become rigid under the 49th-power
   condition?

Do not implement a new descent or iteration in R43 unless an immediate
already-checked contradiction appears.

## Hard stops

- No historical terminal packet or cyclotomic terminal contradiction.
- No assumption that theta depth alone is a well-founded descent measure.
- No claim that a 49th power is impossible.
- No use of global-unit language for the integer scalar `V`.
- No direct full mod-343 seventh-power coordinate expansion unless the
  structured route above fails and the report clearly documents why.
- No `v = 1` from `projectiveLog v = 0`.
- No FLT7 contradiction without a checked independent clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred files

Continue in

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean
```

unless size/heartbeat pressure justifies a focused continuation file.

Neutral coordinate/divisibility lemmas may be moved to a small neutral module
only if they are genuinely packet-independent.

Update the `DkMath.FLT.Seven` facade, API/axiom checks, and a focused R43
scratch file.

Create `report-049.md` and update `ROADMAP.md`.

## Report questions

1. Was `Y = thetaU * (v⁻¹)^7` proved using the same R41 root `v`?
2. Was `quotientCore = thetaSevenUnit * Z^7` proved?
3. Was the depth-32 quotient remainder theorem proved?
4. Were the exact rotation-gap theta coordinate formulas proved?
5. Did depth 32 imply source-root linear and square coordinates are divisible
   by 49?
6. Were the same coordinates of `p.rho^6` shown divisible by 49?
7. Was `49 | thetaSquareInt (Z^7)` proved?
8. Was `7 ∤ V` proved without calling V a global unit?
9. Were `thetaLinearModSeven Z = 0` and
   `thetaSquareModSeven Z = 0` proved?
10. Was the square restriction transported back to
    `thetaSquareModSeven v = 0`?
11. Was `projectiveLog v = 0`, hence `v = w^7`, kernel-checked?
12. Was `W = rho0 * w^49` exposed?
13. Did any independent existing theorem turn this into an actual
    contradiction?

## Outcomes

- Outcome A — projective-root closure combines with an existing independent
  invariant to give an actual contradiction.
- Outcome B — both theta coordinates vanish, `projectiveLog v = 0`,
  `v = w^7`, and `W = rho0*w^49`; no contradiction yet.
- Outcome C — source mod-49 scalarity and quotient depth transport are green,
  but the square-coordinate jet on `Z` is the precise frontier.
- Outcome D — the same-v quotient identity is green, but the depth-32
  remainder/source-coordinate transport is the precise frontier.
- Outcome E — the same-v identity `Y = thetaU*(v⁻¹)^7` is the precise
  frontier.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR43Scratch.lean
git diff --check
```

Print axioms for:

- same-v quotient identity;
- quotientCore seventh-power form;
- depth-32 remainder;
- source-root mod-49 scalarity;
- `49 | thetaSquareInt (Z^7)`;
- `thetaSquareModSeven Z = 0`;
- `thetaSquareModSeven v = 0`;
- `projectiveLog v = 0`;
- `v = w^7`;
- `W = rho0*w^49`.

Run forbidden-source/import scans on all decisive files.
