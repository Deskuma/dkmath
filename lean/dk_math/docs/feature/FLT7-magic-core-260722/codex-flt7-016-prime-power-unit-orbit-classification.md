# FLT7-016 — Prime-power unit-orbit classification

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-015P.

## Status to preserve

- FLT7-015 remains Outcome C for generic `CoprimeTripleRouting` address uniqueness.
- FLT7-015R proves address uniqueness and exact valuation only on `AwayCubicRoutingPacket`.
- FLT7-015P proves that every supplied specialized non-seven depth packet reduces to an actual solution over `ZMod (q^e)` and that an explicit model solution exists in the same row/column family.
- Do not weaken or erase the permanent generic diagonal counterexample.

## Semantic boundary discovered after FLT7-015P

The current type `AwayNonSevenPrimePowerSolubilitySource` stores:

```text
actual solution
normalized cubic root / correction unit
an explicit model solution
```

but it does not yet prove that the actual solution equals the model, or that it is obtained from the model by a canonical unit scaling.

Therefore FLT7-015P establishes full-depth local solubility and a source classification, but not yet completeness of the explicit parametrization.

## Objective

Prove that every actual full-depth prime-power solution lies in the unit-weighted orbit of the canonical explicit model.

The weighted action is:

```text
root coordinates u,v  scale by s^3
endpoint coordinates y,z scale by s^7
```

This preserves all degree-7 / degree-3 equations.

The key arithmetic identity is:

```text
3*5 - 7*2 = 1.
```

For units `C,v,w` satisfying

```text
w^3 = C * v^7,
```

define

```text
s = v^5 * (w⁻¹)^2.
```

Then prove

```text
v = C^2 * s^3,
w = C^5 * s^7.
```

This is the exact inverse parametrization behind the FLT7-014/015P model coordinates.

## New modules and tests

Create:

```text
DkMath/FLT/Seven/PrimePowerUnitOrbit.lean
DkMath/FLT/Seven/PrimePowerOrbitAudit.lean
DkMathTest/FLT/SevenPrimePowerUnitOrbit.lean
DkMathTest/FLT/SevenPrimePowerOrbitAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-016.md
```

Suggested imports:

```lean
-- PrimePowerUnitOrbit.lean
import DkMath.FLT.Seven.PrimePowerCellAudit

-- PrimePowerOrbitAudit.lean
import DkMath.FLT.Seven.PrimePowerUnitOrbit
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Generic 3/7 unit parametrization

Prove a reusable commutative-ring theorem. A suitable surface is:

```lean
theorem unit_three_seven_parametrization
    {R : Type*} [CommRing R]
    {C v w : R}
    (hC : IsUnit C) (hv : IsUnit v) (hw : IsUnit w)
    (h : w ^ 3 = C * v ^ 7) :
    let s := v ^ 5 * (w⁻¹) ^ 2
    IsUnit s ∧ v = C ^ 2 * s ^ 3 ∧ w = C ^ 5 * s ^ 7
```

An equivalent structure-valued result is acceptable.

Requirements:

- do not assume a field;
- use only unit inverse/cancellation;
- prove the displayed formula with ring identities and the equation `h`;
- expose `s` and its unit proof publicly.

Also provide the sign variants through the coefficient `C`; do not duplicate separate algebra for positive and negative cases.

# Part B — Weighted unit action on prime-power solutions

Define a stable action on an existing solution:

```lean
def scalePrimePowerSolution
    {M : ℕ} {row : EndpointRoutingRow} {column : RootRoutingColumn}
    (a : AwayRoutingPrimePowerSolution M row column)
    (s : ZMod M) (hs : IsUnit s) :
    AwayRoutingPrimePowerSolution M row column
```

Coordinates:

```text
u' = a.u * s^3
v' = a.v * s^3
y' = a.y * s^7
z' = a.z * s^7
```

Prove all fields:

- endpoint equation and nondegeneracy;
- root equation and nondegeneracy;
- first-coordinate equation.

Use homogeneity. Do not split into nine unrelated proofs unless dependent matching requires a final finite case split.

Expose identity and composition laws if inexpensive:

```text
scale by 1 = identity
scale by s then t = scale by s*t
```

# Part C — Canonical model constructors

The existing theorems return `Nonempty` model solutions. Add stable model definitions, or package their exact coordinates in a canonical model structure, for:

```text
sevenV, rows y/z/sum
leftCubic from normalized root t
rightCubic from normalized root t
```

For cubic columns use the signed coefficient:

```text
left/y:     C = -49*L(t)
left/z,sum: C =  49*L(t)
right/y:    C =  49*R(t)
right/z,sum:C = -49*R(t)
```

Canonical coordinates are:

```text
v = C^2
u = t*C^2
active endpoint magnitude = C^5
```

with row-dependent zero/sign placement.

Do not use arbitrary `Classical.choice` over the previous `Nonempty` theorem if a direct definition can retain the formulas.

# Part D — Orbit completeness for sevenV

Let `a` be an actual `sevenV` prime-power solution.

For row `y`, its unit coordinates satisfy:

```text
z^3 = u^7.
```

Apply Part A with:

```text
C = 1, v = u, w = z.
```

Obtain a unit `s` and prove:

```text
u = s^3,
z = s^7,
y = 0,
v = 0.
```

For rows `z` and `sum`, use `-u` as the root magnitude and `y` as the endpoint magnitude:

```text
y^3 = (-u)^7.
```

Prove the exact signed coordinates, including `z = -y` in the sum row.

Package a theorem saying the actual solution equals the canonical sevenV model scaled by `s`.

# Part E — Orbit completeness for left cubic

For an actual left-cubic solution:

1. define `t = u * v⁻¹`;
2. reuse the normalized root theorem from FLT7-015P;
3. rewrite `u = t*v` using the unit proof for `v`;
4. rewrite the homogeneous correction:

```text
L(u,v) = v^2 * L(t);
```

5. reduce the first-coordinate equation to one of:

```text
row y:     z^3 = (-49*L(t)) * v^7
row z:     y^3 = ( 49*L(t)) * v^7
row sum:   y^3 = ( 49*L(t)) * v^7 and z = -y.
```

The coefficient `C` is a unit by FLT7-015P.

Apply Part A and obtain a unit `s` with:

```text
v = C^2*s^3
u = t*C^2*s^3
active endpoint = C^5*s^7.
```

Prove that the actual solution equals the canonical left-cubic model scaled by `s`.

# Part F — Orbit completeness for right cubic

Repeat Part E using the right normalized root and correction, with coefficients:

```text
row y:     C =  49*R(t)
row z,sum: C = -49*R(t).
```

Use the existing left/right transform only if it simplifies the proof without obscuring provenance.

# Part G — Strong classification packet

Define a new classification type. Do not silently mutate the semantic meaning of the FLT7-015P source type.

Suggested form:

```lean
inductive AwayNonSevenPrimePowerOrbitSource
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) : RootRoutingColumn → Type
```

Each constructor should retain:

```text
actual solution
canonical model
unit scale s
IsUnit s
exact equality:
  actual = scalePrimePowerSolution model s hs
```

For cubic constructors also retain:

```text
normalized root t
root equation
correction unit
```

Prove:

```lean
theorem primePowerOrbitSource_of_depthPacket
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column)
```

# Part H — Audit route

Define an honest summit preserving the ramified branch:

```lean
inductive PrimePowerOrbitAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayOrbitClassified
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (classification : ∀ p : AwayNonSevenPrimeDepthPacket routing,
        Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column))
```

Prove the route from every `CounterexamplePack`.

# Tests

Focused tests must cover:

- the generic 3/7 unit parametrization in a non-field ring such as `ZMod (5^2)`;
- the weighted action in every row and column;
- all nine orbit-completeness cases;
- exact equality between actual and scaled canonical model;
- preservation of the FLT7-015 generic diagonal counterexample;
- the final audit route;
- public axiom audits.

Do not use `native_decide`.

# Required report

Record:

- Outcome A/B/C;
- the distinction between FLT7-015P source classification and true orbit completeness;
- the generic `3/7` unit parametrization;
- the weighted action;
- all nine completeness cases;
- exact actual/model/scale equality;
- final audit route;
- verification and axiom audit;
- the remaining simultaneous multi-prime/global reconstruction boundary.

# Non-goals

Do not:

- claim that FLT7-015P was false;
- erase or rewrite its source classification;
- generalize prime-address uniqueness to arbitrary routing grids;
- use field-only arguments for `ZMod (q^e)`;
- claim that independently chosen unit scales for different prime addresses glue globally;
- construct `AwayDescentClosureProvider` from single-prime orbit data;
- claim recursive descent or FLT7.

# Outcome classification

- Outcome A: every actual specialized non-seven full-depth solution is exactly a unit-weighted scaling of its canonical explicit model.
- Outcome B: the generic `3/7` parametrization and some columns are complete, but a named orbit-completeness case remains.
- Outcome C: the claimed unit-orbit completeness fails; provide a concrete solution over a prime-power modulus that is not in the proposed orbit.

Commit with a focused message and push to the current feature branch.
