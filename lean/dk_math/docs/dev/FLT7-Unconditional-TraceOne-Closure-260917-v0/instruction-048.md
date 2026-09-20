# FLT7TC-005R42 — Paired-core closure and the second deep-jet coordinate

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-047.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean`
- `PrimeTraceOneDirectRealCubicLocalClass.lean`
- `PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean`
- `PrimeTraceOneDirectRealCubicOrbitSplit.lean`
- `PrimeTraceOneDirectRealCubicOrbit.lean`
- `SevenRealCubicThetaSeventhPowerMod49.lean`
- `SevenRealCubicThetaCoordinates.lean`
- `SevenRealCubicAxisDrop.lean`

R41 ends with an exact current-provenance unit

```text
W = rho * v^7
thetaLinearModSeven v = 0
```

for the `C = 1` branch.  The remaining projective class is therefore
one-dimensional, `(0, lambda)`.

Do **not** attack this by blindly adding a mod-343 trace expansion.  The
quotient side contains much more unused information: the original orbit gap
has theta depth at least 32, while the canonical quotient-core theorem was
previously weakened to theta depth three only for the unit-class calculation.

R42 must close the exact gap/quotient unit product, identify the quotient unit
part with the *same* R41 root `v`, recover enough of the unused depth 32 to
work modulo 49, and force the second theta coordinate of `v` to vanish.

The intended endpoint is

```text
projectiveLog (Additive.ofMul v) = 0
```

and hence an exact second seventh-root extraction

```text
exists w, v = w^7.
```

This is not yet an FLT7 contradiction.

## Part A — fixed unit identity

R41 defines

```text
thetaU := directOrbitDeepJetThetaUnit
rho0   := directOrbitDeepJetRho = -alphaUnit^3.
```

Kernel-check the explicit model identity

```text
thetaSevenUnit = - alpha^2 * (1 + alpha)
```

and, preferably at the unit level,

```text
thetaU = (-1) * alphaUnit^2 * alphaAddOneUnit.
```

Use the existing exact definition

```text
orbitUnit01 =
  (pairAxisUnit 1 - 1) * alphaAddOneInv * thetaSevenUnit^5
```

together with `pairAxisUnit 1 = 1 + alpha` to prove the decisive fixed-unit
cancellation

```text
orbitUnit01Unit * thetaU⁻¹^3 * rho0⁻¹ = thetaU.
```

Equivalent reassociation / inverse spelling is acceptable.

This identity must be literal in `SevenRealCubicIntˣ`, not only a
projective-log equality.

## Part B — quotient-side unit part under C = 1

For a canonical packet `h : DirectOrbitCanonicalCommonFactorPacket p` with
`hc : h.c = 1`, take scalarizing units

```text
gapSquareRoot      = eta * U
quotientSquareRoot = xi  * V.
```

Reuse R39 for `eta` and `xi`.

Define

```text
Y :=
  h.squareRefinement.powerSplit.quotientUnit *
    (h.squareRefinement.quotientSquareUnit * xi^2)^7
```

as a model unit.

Prove

```text
h.squareRefinement.powerSplit.quotientCore
  = (Y : SevenRealCubicInt) * (h.v : SevenRealCubicInt)^14.
```

Similarly reuse the existing R40 definition `X = directOrbitDeepJetXUnit ...`
and its gap-side scalarization

```text
gapCore = X * U^14.
```

Add the latter theorem explicitly if it is not already public.

## Part C — exact paired-unit product

Use

```text
cores_product_eq
a = U*V                       -- from C=1
```

to cancel the nonzero rational scalar `a^14 = (U*V)^14` and prove the exact
unit identity

```text
X * Y =
  orbitUnit01Unit *
    thetaU ^ (7 * (1 + 2*k)),
```

where `k = h.squareRefinement.powerSplit.gapSplit.k`.

Do not infer this from projective classes.

The scalar cancellation must use the checked positivity/nonzeroness of the
canonical `U,V,a`.

## Part D — the same R41 root appears on the quotient side

Let `v` satisfy the R41 exact equality

```text
W = rho0 * v^7.
```

Recall

```text
W = thetaU⁻¹^(10 + 14*k) * X.
```

Combine Part C, the exponent identity, and Part A to prove

```text
Y = thetaU * v⁻¹^7.
```

Equivalent `thetaU * (v⁻¹)^7` spelling is preferred.

This is a mandatory R42 bridge.  There must be no extra existential seventh
root and no unidentified fixed unit.

Consequently prove

```text
quotientCore =
  thetaSevenUnit *
    ((v⁻¹ : SevenRealCubicInt) * (V : SevenRealCubicInt)^2)^7.
```

Define the element

```text
Z := (v⁻¹ : SevenRealCubicInt) * (V : SevenRealCubicInt)^2.
```

Then expose simply

```text
quotientCore = thetaSevenUnit * Z^7.
```

## Part E — restore the unused depth-32 quotient remainder

The existing theorem
`directOrbitPowerSplit_quotientCore_eq_canonical_axis3` deliberately weakens
the construction to `theta^3 | d`.

Return to the same construction based on

```text
directOrbit_gap_axis_pow32_dvd p
```

and expose a stronger current-provenance theorem, conceptually:

```text
exists d,
  eisensteinAxis^31 | d
  and quotientCore = directOrbitQuotientCoreCanonical p d.
```

Then prove

```text
eisensteinAxis^32 |
  quotientCore - thetaSevenUnit * p.rho^6.
```

Reason: in the canonical expansion the first omitted term is

```text
3 * thetaSevenUnit * theta * d * p.rho^5,
```

and `theta^31 | d`; every later term is deeper.

Do not use historical terminal packets.

## Part F — neutral theta-power-to-integer-power helpers

From

```text
7 = eisensteinAxis^3 * thetaSevenUnit
IsUnit thetaSevenUnit
```

prove small neutral lemmas sufficient for this checkpoint:

```text
eisensteinAxis^6 | x -> (49 : SevenRealCubicInt) | x
eisensteinAxis^9 | x -> (343 : SevenRealCubicInt) | x.
```

Equivalently prove `Associated (theta^6) 49` and
`Associated (theta^9) 343`.

Do not introduce a general valuation theory.

## Part G — the source orbit root is scalar modulo 49

For an arbitrary model element written in theta coordinates

```text
r0 = A + B*theta + C*theta^2,
```

kernel-check the exact rotation-gap coordinate formulas

```text
thetaConstInt  (rotate r0 - r0) = -7*C
thetaLinearInt (rotate r0 - r0) = 3*B - 21*C
thetaSquareInt (rotate r0 - r0) = B - 6*C.
```

Apply these to `p.rho`.

Since

```text
theta^32 | rotate(p.rho) - p.rho,
```

we also have `theta^9 |` the gap; by Part F,

```text
343 | rotate(p.rho) - p.rho
```

as a model-ring scalar divisibility statement.

Transport this to integral theta coordinates and prove

```text
49 | thetaLinearInt p.rho
49 | thetaSquareInt p.rho.
```

Suggested arithmetic:

- `343 | -7*C` gives `49 | C`;
- `343 | B - 6*C` and `49 | C` give `49 | B`.

Then prove

```text
49 | thetaLinearInt (p.rho^6)
49 | thetaSquareInt (p.rho^6).
```

A preferred proof is to show

```text
(49 : SevenRealCubicInt) |
  p.rho - ofInt (thetaConstInt p.rho)
```

and factor the difference of sixth powers.  Avoid a large direct sixth-power
coordinate expansion if possible.

## Part H — quotient depth gives a mod-49 square-coordinate equation for Z

Combine Parts D and E:

```text
theta^32 |
  thetaSevenUnit * (Z^7 - p.rho^6).
```

Cancel the unit `thetaSevenUnit` and weaken to `theta^6`:

```text
theta^6 | Z^7 - p.rho^6.
```

By Part F,

```text
49 | Z^7 - p.rho^6.
```

Therefore, using Part G,

```text
49 | thetaSquareInt (Z^7).
```

Expose this as a stable theorem.

## Part I — local seven-unit status of V and Z

Use

```text
directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd
quotientSquareRoot = xi * V
```

to prove

```text
¬ 7 | V.
```

If `7 | V`, then `theta | (V : SevenRealCubicInt)` follows immediately
from `7 = theta^3 * thetaSevenUnit`, contradicting the square-root theorem
after multiplication by the unit `xi`.

Consequently

```text
(thetaConstInt Z : ZMod 7) != 0.
```

Also transport the R41 endpoint through inversion and scalar multiplication:

```text
thetaLinearModSeven Z = 0.
```

Do not assume `Z` is a global unit; it is only a theta-local unit because
`7 ∤ V`.

## Part J — force the second coordinate of Z

Let

```text
A := thetaConstInt Z
B := thetaLinearInt Z
C := thetaSquareInt Z.
```

Use

```text
thetaSquare_pow_seven_mod49_neutral A B C
```

and Part H to obtain

```text
49 | 7 * (C*A^6 + 3*B^2*A^5).
```

Cancel one factor seven and reduce modulo seven.

Part I gives

```text
B = 0 mod 7
A != 0 mod 7.
```

Therefore prove

```text
C = 0 mod 7,
```

i.e.

```text
thetaSquareModSeven Z = 0.
```

This is the second genuinely new deep-jet restriction.

## Part K — transport the second coordinate back to v

Write

```text
Z = v⁻¹ * V^2
```

and use the theta multiplication laws.

Because the scalar `V^2` has nonzero theta constant modulo seven and zero
linear/square coordinates, Part J implies

```text
thetaSquareModSeven (v⁻¹ : SevenRealCubicInt) = 0.
```

Use

```text
v * v⁻¹ = 1,
thetaLinearModSeven v = 0
```

and the product formulas to conclude

```text
thetaSquareModSeven (v : SevenRealCubicInt) = 0.
```

Hence prove the mandatory endpoint

```text
projectiveLog (Additive.ofMul v) = 0.
```

Since the first nilpotent coordinate is zero, the quadratic correction in
`projectiveLog` is also zero.

Finally apply

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

to obtain

```text
exists w : SevenRealCubicIntˣ, v = w^7.
```

Thus the R41 correction strengthens from

```text
W = rho0 * v^7
```

to

```text
W = rho0 * w^49.
```

Expose the latter if cheap.

## Part L — provenance-preserving packet

Prefer a small structure or theorem collecting, for every current
`C = 1` canonical packet:

```text
eta xi v w
gapSquareRoot      = eta * U
quotientSquareRoot = xi * V
W = rho0 * v^7
v = w^7
thetaLinearModSeven v = 0
thetaSquareModSeven v = 0
projectiveLog v = 0
quotientCore = thetaSevenUnit * ((v⁻¹)*V^2)^7.
```

Do not duplicate the canonical arithmetic fields.

## Part M — clash audit

After the full zero projective class is green, inspect current checked data
only:

1. Does `W = rho0 * w^49` contradict the R27 non-square theorem for
   coefficient zero after removing the known even-power factors?
2. Does the R27 mixed real signature fix the sign class strongly enough to
   exclude a 49th-power correction?
3. Can the same trace/quotient pair be iterated once more without new
   provenance?
4. Does the optional Thue normal form become rigid under the stronger
   49th-power correction?

Do not force a contradiction.  A 49th-power correction by itself is not
impossible.

## Hard stops

- No historical terminal/cyclotomic routing packet as a hidden premise.
- Do not replace the actual depth-32 construction by the older weakened
  depth-three theorem.
- No inference from equal projective classes when a literal unit identity is
  required.
- Do not assume `V` is a global unit; prove only its theta-local unit status.
- No direct mod-343 brute-force expansion unless the small neutral route above
  genuinely fails.
- Do not infer `v = 1` from `projectiveLog v = 0`.
- Do not call a 49th power a contradiction.
- No successor/descent claim.
- No FLT7 contradiction without an actual checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred implementation

Continue the current-provenance layer in a new focused file if the existing
DeepJet file becomes too large:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean
```

Neutral theta-power/scalar-divisibility helpers may live in
`SevenRealCubicAxisDrop.lean` only if genuinely packet-independent.

Keep `SevenRealCubicThetaSeventhPowerMod49.lean` limited to neutral
seventh-power coordinate statements.

Update the `DkMath.FLT.Seven` facade and focused API/axiom/scratch tests.

Create `report-048.md` and update `ROADMAP.md`.

## Report questions

1. Was the literal fixed-unit identity
   `orbitUnit01 * thetaU⁻³ * rho0⁻¹ = thetaU` proved?
2. Were the gap/quotient scalarized unit parts `X,Y` exposed?
3. Was `X*Y` computed exactly from `cores_product_eq`?
4. Was the quotient unit part reduced to
   `Y = thetaU * v⁻⁷` using the *same* R41 root `v`?
5. Was
   `quotientCore = thetaSevenUnit * ((v⁻¹)*V²)^7` proved?
6. Was the unused canonical quotient depth restored to
   `theta^32 | quotientCore - thetaSevenUnit*p.rho^6`?
7. Did the original orbit gap force
   `49 | thetaLinearInt p.rho` and
   `49 | thetaSquareInt p.rho`?
8. Was `49 | thetaSquareInt (Z^7)` proved?
9. Was `7 ∤ V` proved from the quotient square-root axis exclusion?
10. Was `thetaSquareModSeven Z = 0` proved from the neutral mod-49 square jet?
11. Was this transported back to
    `thetaSquareModSeven v = 0`?
12. Was `projectiveLog v = 0`, hence `v = w^7`, kernel-checked?
13. Did any independent existing invariant turn the resulting 49th-power
    correction into an actual contradiction?

## Outcomes

- Outcome A — the second-coordinate closure plus an independent existing
  invariant yields an actual contradiction.
- Outcome B — the paired-core bridge is green, both theta coordinates of
  `v` vanish, and `v = w^7`; no contradiction yet.
- Outcome C — the exact quotient identity with the same `v` is green, but
  restoring/transporting depth 32 to mod 49 is the precise frontier.
- Outcome D — depth transport is green, but the mod-49 square-coordinate
  extraction for `Z` is the precise frontier.
- Outcome E — the exact paired-unit product/fixed-unit cancellation is the
  precise frontier.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR42Scratch.lean
git diff --check
```

If implementation stays in the existing DeepJet module, adjust focused build
names accordingly.

Print axioms for:

- fixed unit cancellation;
- exact `X*Y` product;
- exact quotient identity with the same `v`;
- depth-32 quotient remainder;
- source-root mod-49 scalarity;
- `thetaSquareModSeven Z = 0`;
- `thetaSquareModSeven v = 0`;
- `projectiveLog v = 0`;
- `v = w^7`.

Run forbidden-source/import scans on every decisive file.
