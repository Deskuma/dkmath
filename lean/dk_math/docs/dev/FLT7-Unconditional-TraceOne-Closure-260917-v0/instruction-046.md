# FLT7TC-005R40 — Weighted cyclic trace and the first mod-49 seventh-power jet

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-045.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `PrimeTraceOneDirectRealCubicSuccessorAudit.lean`
- `PrimeTraceOneDirectRealCubicLocalClass.lean`
- `SevenRealCubicThetaCoordinates.lean`
- `SevenRealCubicThetaSeventhPower.lean`
- `SevenRealCubicAxisDrop.lean`
- `SevenRealCubicUnitClass.lean`

R39 proves the `C = 1` scalarization and reduces R27 to a unit-only cyclic
three-term equation.  Its existing mod-7 theta residue/linear/square
coordinates all cancel.  No current-provenance mod-49 bridge was found in
the terminal packet tower.

R40 must build the deeper bridge directly from the neutral
`SevenRealCubicInt` arithmetic already present in the repository.

The key observation is that the R39 equation is a weighted cyclic trace.
After multiplying by the exact ramified-axis power and using

```text
7 = eisensteinAxis^3 * thetaSevenUnit,
```

the equation normalizes to an exact trace-zero condition for `theta^2 * W`,
where `W` is a global unit with signed norm `1` and projective class `(1,1)`.

The existing exact seventh-power theta-coordinate formulas then provide the
first genuinely new mod-49 restriction.

## Goal

For every R39 `C = 1` state, construct a unit `W` satisfying

```text
cyclicTrace (eisensteinAxis^2 * W) = 0
norm W = 1
projectiveLog W = (1,1).
```

Convert the trace equation to exact integral theta coordinates

```text
3*A - 10*B + 35*C = 0.
```

Then use the explicit representative

```text
rho := - alphaUnit^3
```

to write

```text
W = rho * v^7
```

for a global unit `v`, and prove the first deeper jet constraint

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0.
```

Equivalently, the first coordinate of `projectiveLog v` vanishes.

Also expose the resulting binary cubic / Thue normal form as a precise
global arithmetic frontier.

Stop there unless an already checked theorem gives an immediate contradiction.

## Part A — compress the R39 unit equation

Let

```text
t := h.squareRefinement
s := t.powerSplit
k := s.gapSplit.k
e := 32 + 42*k.
```

Given the R39 scalarizing unit `eta`, define conceptually

```text
rootUnit := t.gapSquareUnit * eta^2
X := s.gapUnit * rootUnit^7.
```

Prove literal identities identifying the three R39 terms as

```text
X,
P^e * rotate(X),
P^e * rotate(P^e) * rotate^2(X),
```

where

```text
P := directOrbitPairAxisUnitOne.
```

Use the existing definitions of `directOrbitTwistedCoeff*`,
`directOrbitSquareTwistCoeff*`, and `directOrbitRotateUnit`.

Do not introduce an arbitrary new coefficient triple.

## Part B — neutral cyclic trace

Define in the model ring

```text
def directOrbitCyclicTrace (x : SevenRealCubicInt) : SevenRealCubicInt :=
  x + rotateEquiv x + rotateEquiv (rotateEquiv x)
```

or an equivalent neutral name if a suitable definition already exists.

Prove the basic additive/scalar transport needed below, including that integer
scalars are fixed by rotation.

Use the existing theorems

```text
directOrbit_rotate_axis_pow
directOrbit_rotate_twice_axis_pow
```

to convert the Part A equation into

```text
directOrbitCyclicTrace (eisensteinAxis^e * X) = 0.
```

This theorem should be literal, not only after applying a coordinate map.

## Part C — normalize the ramified exponent

Define

```text
n := 10 + 14*k.
```

Kernel-check

```text
e = 3*n + 2.
```

Let

```text
thetaUnit : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit.
```

From

```text
7 = eisensteinAxis^3 * thetaSevenUnit
```

prove a literal normalization of the shape

```text
eisensteinAxis^e * X =
  (7 : SevenRealCubicInt)^n * eisensteinAxis^2 * W
```

where

```text
W := thetaUnit⁻¹^n * X
```

up to harmless reassociation / power spelling.

Since the model ring is a domain and `7^n != 0`, cancel the rational scalar
from the cyclic-trace equation and prove

```text
directOrbitCyclicTrace (eisensteinAxis^2 * W) = 0.
```

Do not appeal to historical terminal depth packets.

## Part D — invariants of W

Prove `W` is represented by an explicit model unit.

Then prove:

```text
norm W = 1
projectiveLog (Additive.ofMul Wunit) = (1,1).
```

For the norm:

- reuse `directOrbit_squareTwist_coeff0_norm_eq_one` to identify the signed
  norm of the first R39 term `X` as `1`;
- prove or reuse `norm thetaSevenUnit = -1`;
- `n = 10 + 14*k` is even, hence the normalizing theta-unit contributes norm
  `1`.

For the projective class:

- `X` has the same class `(2,4)` as square-twist coefficient zero because
  `eta^14` is a seventh power;
- reuse `thetaSevenUnit_projectiveLog = (5,1)`;
- `n % 7 = 3`;
- calculate

```text
(2,4) - 3*(5,1) = (1,1)  in (ZMod 7)^2.
```

Keep signed norm and `natAbs` norm separate.

## Part E — exact cyclic-trace coordinate formula

Prove a neutral coordinate theorem for arbitrary `A B C : Int`:

```text
directOrbitCyclicTrace
  (eisensteinAxis^2 * ofThetaCoordinates A B C)
=
  ofInt (7 * (3*A - 10*B + 35*C)).
```

Equivalent coefficient spelling is acceptable.

Preferred proof: direct coordinate normalization using the concrete
`rotateEquiv`, `eisensteinAxis`, and `ofThetaCoordinates` APIs.

Apply this to `W` through `theta_coordinate_decomposition` and the Part C
trace-zero theorem.  Since integer casting into the model is injective, obtain

```text
3 * thetaConstInt W
  - 10 * thetaLinearInt W
  + 35 * thetaSquareInt W = 0.
```

This exact integer equation is mandatory.

## Part F — explicit class-(1,1) representative

Define the model unit

```text
rho : SevenRealCubicIntˣ := (-1) * alphaUnit^3.
```

Kernel-check:

```text
(rho : SevenRealCubicInt) = ofThetaCoordinates (-20) (-13) (-2)
norm (rho : SevenRealCubicInt) = 1
projectiveLog (Additive.ofMul rho) = (1,1)
directOrbitCyclicTrace (eisensteinAxis^2 * (rho : SevenRealCubicInt)) = 0.
```

The final line is an important calibration: the trace/norm/class packet is
arithmetically consistent and is not itself a contradiction.

Because `W` and `rho` have equal projective class, use

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

on `W * rho⁻¹` (or the equivalent orientation) to prove an exact global
seventh-power correction:

```text
exists v : SevenRealCubicIntˣ,
  W = rho * v^7.
```

Do not replace equality of projective classes by literal equality.

## Part G — complete the neutral mod-49 seventh-power theta jet

`SevenRealCubicThetaSeventhPower.lean` already proves exact formulas

```text
thetaLinearInt (x^7) = 7 * seventhThetaLinearQuotient ...
thetaSquareInt (x^7) = 7 * seventhThetaSquareQuotient ...
```

and their quotient reductions mod seven.

Add the missing neutral constant-coordinate statement for

```text
x = ofThetaCoordinates A B C.
```

Preferred stable statements are integer congruences/divisibilities:

```text
49 | thetaConstInt (x^7) - A^7

49 | thetaLinearInt (x^7) - 7 * B * A^6

49 | thetaSquareInt (x^7)
       - 7 * (C*A^6 + 3*B^2*A^5).
```

The latter two should be derived from the existing exact quotient formulas
and their mod-seven factor theorems rather than re-expanding the seventh
power from scratch.

For the constant coordinate, a focused direct coordinate proof is acceptable.
Do not create a general p-adic library.

Optionally package these three congruences as a small neutral
`ThetaSeventhPowerJetMod49` theorem/structure.

## Part H — first genuinely deeper constraint

Let

```text
v0 := (v : SevenRealCubicInt)
A := thetaConstInt v0
B := thetaLinearInt v0
C := thetaSquareInt v0.
```

First prove

```text
(A : ZMod 7) != 0
```

from `thetaConstModSeven_unit_ne_zero`.

Use the Part G mod-49 seventh-power jet and the explicit theta coordinates of
`rho` to prove the congruence

```text
49 |
  (3*thetaConstInt (rho * v0^7)
    - 10*thetaLinearInt (rho * v0^7)
    + 35*thetaSquareInt (rho * v0^7))
  - 21 * A^6 * B.
```

Equivalent `ZMod 49` spelling is acceptable.

Now substitute

```text
W = rho * v^7
```

and the exact Part E trace-plane equation for `W`.  Deduce

```text
7 | B.
```

Hence expose the public consequence

```text
thetaLinearModSeven (v : SevenRealCubicInt) = 0.
```

and, if cheap,

```text
exists y : ZMod 7,
  projectiveLog (Additive.ofMul v) = (0,y).
```

This is the first nontrivial local restriction beyond the R39 theta^3
cancellation and is a mandatory R40 target.

## Part I — exact binary cubic / Thue frontier

Let

```text
A := thetaConstInt W
B := thetaLinearInt W
C := thetaSquareInt W.
```

From

```text
3*A - 10*B + 35*C = 0
```

prove an integral two-parameter representation

```text
exists r s : Int,
  A = 5*(r+s) and
  B = 5*r - 2*s and
  C = r - s.
```

A convenient division-free derivation is to obtain divisibility by `3` of
`B-2*C` and `B-5*C`, then set the corresponding witnesses to `r` and `s`.

Using the explicit theta-coordinate norm polynomial, prove

```text
norm W =
  -r^3 + 4*r^2*s + 11*r*s^2 - 43*s^3.
```

Since `norm W = 1`, expose the Thue equation

```text
r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3 = -1.
```

From `projectiveLog W = (1,1)`, prove at least the congruence

```text
(r : ZMod 7) = 3 * (s : ZMod 7),
```

or the equivalent integer divisibility `7 | r - 3*s`.

Do not claim a classification of all integer solutions unless it is actually
proved.

Calibration:

```text
r = -3, s = -1
```

corresponds to `W = rho` and satisfies the equation.  Kernel-check this
example in scratch or production.

Therefore the Thue equation plus the `(1,1)` class is not to be called a
contradiction without a genuine uniqueness/classification theorem.

## Part J — clash audit

After Parts A–I are green, audit only existing checked data.

Questions:

1. Does `thetaLinearModSeven v = 0` combine with an independent current
   theorem fixing the first projective coordinate of this seventh root?
2. Does the R27 non-square/mixed-sign theorem determine the second coordinate
   of `projectiveLog v`?
3. Does the quotient scalarization unit `xi` give a second independent
   mod-49 jet equation for the same `v` or a canonically related unit?
4. Is the Thue equation already covered by a proved DkMath cubic carrier or
   finite classification?
5. Can an existing neutral norm-first-variation theorem apply directly to
   this current-provenance `W` without importing terminal routing hypotheses?

Do not start a general Thue solver, Baker theory, or a new reciprocity theory
inside R40.

## Preferred files

New focused current-provenance file:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean
```

Neutral mod-49 additions belong in:

```text
DkMath/FLT/Seven/SevenRealCubicThetaSeventhPower.lean
```

only if they are genuinely packet-independent.

Export stable declarations through `DkMath.FLT.Seven`.

Add focused API/axiom tests and an R40 scratch file.

Create `report-046.md` and update `ROADMAP.md`.

## Hard stops

- No historical terminal/cyclotomic packet as a hidden premise.
- No claim that the R39 three theta-coordinate cancellation was itself a
  contradiction.
- No claim that trace zero + norm one + class `(1,1)` is impossible;
  `rho = -alpha^3` is an explicit calibration witness.
- No equality of units merely from equal projectiveLog.
- No division by `7`, `49`, or a theta power without an exact divisibility
  witness.
- No unbounded brute-force search promoted to a theorem.
- No Thue-solution classification unless kernel-checked.
- No successor/descent claim.
- No FLT7 contradiction without an actual checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Report questions

1. Was the R39 unit equation compressed to one unit `X` and its two cyclic
   rotations with the exact transport weights?
2. Was it converted to a literal cyclic trace of `theta^e * X`?
3. Was the exponent normalized with `7 = theta^3 * thetaSevenUnit` to a
   trace-zero `theta^2 * W`?
4. Were `norm W = 1` and `projectiveLog W = (1,1)` proved?
5. Was the exact trace-plane equation `3A-10B+35C=0` proved?
6. Was `rho = -alpha^3` checked as a consistent norm-one class-(1,1)
   trace-plane witness?
7. Was `W = rho * v^7` proved with an exact global unit `v`?
8. Were the three neutral seventh-power theta coordinates completed modulo
   49?
9. Was `thetaLinearModSeven v = 0` proved?
10. Was the binary cubic equation
    `r^3 - 4r^2s - 11rs^2 + 43s^3 = -1` exposed with
    `r = 3s mod 7`?
11. Did any independent existing invariant close a contradiction?

## Outcomes

- Outcome A — the weighted-trace/deep-jet reduction plus an independent
  checked invariant yields an actual contradiction.
- Outcome B — weighted trace, norm/class normalization, mod-49 jet,
  `thetaLinearModSeven v = 0`, and the Thue frontier are green; no
  contradiction yet.
- Outcome C — weighted trace and the exact trace/norm/class packet are green,
  but the neutral mod-49 seventh-power jet is the precise frontier.
- Outcome D — the mod-49 jet is green, but transporting it through
  `W = rho*v^7` to force the linear coordinate is the precise frontier.
- Outcome E — the weighted cyclic-trace normalization itself is the precise
  missing bridge.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJetR40Scratch.lean
git diff --check
```

Print axioms for:

- weighted cyclic-trace theorem;
- normalized `theta^2 * W` trace-zero theorem;
- `norm W = 1`;
- `projectiveLog W = (1,1)`;
- exact trace-plane coordinate theorem;
- `W = rho * v^7`;
- each neutral mod-49 seventh-power jet theorem;
- `thetaLinearModSeven v = 0`;
- the Thue normal-form theorem.

Run forbidden-source/import scans on every decisive file.
