# FLT7-015P — Specialized prime-power cell lift

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-015R.

## Status to preserve

- FLT7-014 remains complete: every actual non-seven first-residue witness belongs to an explicit soluble family.
- FLT7-015 remains Outcome C: generic prime-address uniqueness for arbitrary `CoprimeTripleRouting` is false.
- FLT7-015R repairs address uniqueness and exact valuation isolation only on `AwayCubicRoutingPacket`.

Do not generalize the repaired address theorem back to the generic routing structure.

## Objective

For a specialized non-seven prime address with exact positive exponent

```text
q, row, column, e
```

coming from `AwayRoutingPrimeDepthPacket`, set

```text
M = q^e.
```

Prove that the actual endpoint/root coordinates reduce to a full-depth local
solution over `ZMod M`, not merely over `ZMod q`.

Then lift the FLT7-014 explicit soluble families from `ZMod q` to `ZMod (q^e)`.
The target conclusion is:

```text
Every actual non-seven addressed cell is locally soluble at its complete
q-adic cell depth.
```

This checkpoint concerns one prime at one specialized address. It does not
solve simultaneous global signed reconstruction.

## New modules and tests

Create:

```text
DkMath/FLT/Seven/PrimePowerCellSystems.lean
DkMath/FLT/Seven/PrimePowerCellSolubility.lean
DkMath/FLT/Seven/PrimePowerCellAudit.lean
DkMathTest/FLT/SevenPrimePowerCellSystems.lean
DkMathTest/FLT/SevenPrimePowerCellAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-015p.md
```

Suggested imports:

```lean
-- PrimePowerCellSystems.lean
import DkMath.FLT.Seven.SpecializedPrimeAddress

-- PrimePowerCellSolubility.lean
import DkMath.FLT.Seven.PrimePowerCellSystems

-- PrimePowerCellAudit.lean
import DkMath.FLT.Seven.PrimePowerCellSolubility
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Non-seven specialized depth packet

Define a wrapper that preserves the specialized address and excludes the
ramified prime:

```lean
structure AwayNonSevenPrimeDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  depth : AwayRoutingPrimeDepthPacket r
  q_ne_seven : depth.address.q ≠ 7
```

Expose abbreviations or accessors:

```lean
q       := depth.address.q
row     := depth.address.row
column  := depth.address.column
exponent := depth.exponent
modulus := q ^ exponent
```

Prove:

```lean
theorem AwayNonSevenPrimeDepthPacket.q_prime ... : Nat.Prime p.q
```

```lean
theorem AwayNonSevenPrimeDepthPacket.exponent_pos ... : 0 < p.exponent
```

```lean
theorem AwayNonSevenPrimeDepthPacket.modulus_pos ... : 0 < p.modulus
```

```lean
theorem AwayNonSevenPrimeDepthPacket.modulus_ne_one ... : p.modulus ≠ 1
```

# Part B — Exact prime-power divisibility at the addressed cell

From

```text
exponent = padicValNat q cell
```

prove:

```lean
theorem AwayNonSevenPrimeDepthPacket.modulus_dvd_cell ... :
    p.modulus ∣ routingCell r.routing p.row p.column
```

Also expose maximality:

```lean
theorem AwayNonSevenPrimeDepthPacket.next_power_not_dvd_cell ... :
    ¬ p.q ^ (p.exponent + 1) ∣ routingCell r.routing p.row p.column
```

Use existing `padicValNat` APIs. Do not reimplement valuation theory.

Transfer exact depth to the outer factors using FLT7-015R:

```lean
theorem AwayNonSevenPrimeDepthPacket.modulus_dvd_endpoint ... :
    p.modulus ∣ endpointRoutingFactorNat y z p.row
```

```lean
theorem AwayNonSevenPrimeDepthPacket.modulus_dvd_root ... :
    p.modulus ∣ rootRoutingFactorNat r p.column
```

Prove that the next power does not divide either outer factor as a consequence
of the exact depth equalities.

# Part C — Unit facts for the two nonaddressed rows and columns

A natural integer `a` whose `q`-valuation is zero should become a unit in
`ZMod (q^e)`.

Prove a reusable specialized lemma:

```lean
theorem isUnit_zmod_primePower_of_not_dvd
    {q e a : ℕ} (hq : Nat.Prime q) (he : 0 < e)
    (ha : ¬ q ∣ a) : IsUnit (a : ZMod (q^e))
```

An equivalent theorem using `Nat.Coprime a (q^e)` is acceptable.

For a depth packet, prove:

```text
- every endpoint factor outside `p.row` is a unit modulo `p.modulus`;
- every root factor outside `p.column` is a unit modulo `p.modulus`.
```

Use specialized prime-address uniqueness, outer coprimality, or the exact depth
packet. Do not rely on generic diagonal uniqueness.

It is strongly recommended to expose:

```lean
theorem AwayRoutingPrimeAddress.not_dvd_other_cell
    ...
    (haddress : row' ≠ a.row ∨ column' ≠ a.column) :
    ¬ a.q ∣ routingCell r.routing row' column'
```

This is a small stable convenience theorem derivable directly from `a.unique`.

# Part D — Prime-power local-system surface

Do not reuse the old first-residue structures unchanged: over a composite
modulus, `x ≠ 0` is weaker than being a unit.

Define unit-based versions over an arbitrary modulus `M`:

```lean
def AwayEndpointPrimePowerNondegenerate (M : ℕ) :
    EndpointRoutingRow → ZMod M → ZMod M → Prop
```

with:

```text
Y row:   IsUnit z
Z row:   IsUnit y
Sum row: IsUnit y ∧ IsUnit z
```

Define `AwayEndpointPrimePowerEquation` with the same three zero equations.

Define:

```lean
def AwayRootPrimePowerNondegenerate (M : ℕ) :
    RootRoutingColumn → ZMod M → ZMod M → Prop
```

with:

```text
sevenV:     IsUnit u
leftCubic:  IsUnit v
rightCubic: IsUnit v
```

Define `AwayRootPrimePowerEquation` and
`AwayFirstCoordinatePrimePowerEquation` by the same polynomial formulas as
FLT7-014, now in `ZMod M`.

Package:

```lean
structure AwayRoutingPrimePowerSolution
    (M : ℕ) (row : EndpointRoutingRow)
    (column : RootRoutingColumn) : Type where
  u v y z : ZMod M
  endpoint_nondegenerate : AwayEndpointPrimePowerNondegenerate M row y z
  endpoint_equation : AwayEndpointPrimePowerEquation M row y z
  root_nondegenerate : AwayRootPrimePowerNondegenerate M column u v
  root_equation : AwayRootPrimePowerEquation M column u v
  first_coordinate_equation :
    AwayFirstCoordinatePrimePowerEquation M row column u v y z
```

# Part E — Reduction of an actual full-depth address

Construct the actual reduction:

```lean
noncomputable def AwayNonSevenPrimeDepthPacket.toPrimePowerSolution
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwayNonSevenPrimeDepthPacket r) :
    AwayRoutingPrimePowerSolution p.modulus p.row p.column
```

Use the original integers:

```text
u = root.fst
v = root.snd
y = endpoint y
z = endpoint z
```

reduced modulo `p.modulus`.

Required proof architecture:

1. endpoint equation follows from `p.modulus_dvd_endpoint` and the selected row;
2. root equation follows from `p.modulus_dvd_root` and the selected column;
3. first-coordinate equation follows because the addressed cell divides the
   FLT7-013 exact remainder and `p.modulus ∣ cell`;
4. endpoint unit facts follow from endpoint outer pairwise coprimality;
5. root unit facts follow from root outer pairwise coprimality.

For the `sevenV` column, use `q ≠ 7` to remove the visible factor `7` and show
`q^e ∣ vPart`; bridge `vPart = natAbs root.snd` to the signed coordinate.

For cubic columns, `vPart` is coprime to the addressed cubic factor, so the
root second coordinate is a unit modulo `q^e`.

# Part F — Normalized cubic root at full depth

For an actual left-cubic packet, define

```text
t = u / v in ZMod (q^e)
```

using the unit inverse of `v`, and prove:

```lean
leftCubicNormalizedZMod t = 0
```

where a modulus-polymorphic normalized polynomial may be reused or generalized.
The proof should use homogeneous factorization:

```text
P(u,v) = v^3 * P(u/v).
```

Similarly for the right cubic.

Do not divide in integers. Division belongs only in `ZMod (q^e)` after the
unit proof.

# Part G — Correction is a unit at every finite non-seven depth

Lift the integer Bezout certificates:

```text
A(t)P(t) + B(t)L(t) = 7,
A'(t)Q(t) + B'(t)R(t) = 7.
```

Prove that `7` is a unit in `ZMod (q^e)` for `q ≠ 7`.
Then prove:

```lean
theorem leftCorrection_isUnit_of_leftCubic_eq_zero_primePower ...
```

```lean
theorem rightCorrection_isUnit_of_rightCubic_eq_zero_primePower ...
```

A product equal to the unit `7` forces the correction factor to be a unit.
Use standard `IsUnit` APIs; do not assume the ring is a field.

# Part H — Explicit soluble families over `ZMod (q^e)`

Generalize the FLT7-014 scale construction to any prime-power modulus.

For `sevenV`, construct all three rows using unit scale `1` exactly as before.

For the left cubic, given a normalized root `t` and the unit correction `L`, set

```text
C = ±49*L,
v = C^2,
u = t*C^2,
endpoint magnitude = C^5.
```

Since `q ≠ 7`, both `49` and `L` are units, hence `C` is a unit. Prove all three
row solutions.

Do the transformed construction for the right cubic.

Suggested theorem surface:

```lean
nonempty_primePowerSolution_sevenV
```

```lean
nonempty_primePowerSolution_leftCubic_of_root
```

```lean
nonempty_primePowerSolution_rightCubic_of_root
```

# Part I — Full-depth classification and summit

Define a provenance type analogous to FLT7-014:

```lean
inductive AwayNonSevenPrimePowerSolubilitySource ...
```

with constructors:

```text
sevenV
leftCubic  (normalized root modulo q^e)
rightCubic (normalized root modulo q^e)
```

Prove that every actual non-seven depth packet belongs to one of these full-depth
families.

Package the final audit route:

```lean
inductive PrimePowerCellAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayPrimePowerSoluble
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (depth : AwayNonSevenPrimeDepthPacket routing)
      (source : AwayNonSevenPrimePowerSolubilitySource depth)
  | awaySevenOnly
      (routing : AwayCubicRoutingPacket x y z)
      -- no non-seven nontrivial cell was selected
```

The exact summit shape may be adjusted because a routing grid may have several
non-seven primes. Do not use `Classical.choice` to pretend that a non-seven
address exists if every nontrivial support is seven-primary. An honest theorem
may instead be parameterized by a supplied `AwayNonSevenPrimeDepthPacket`.

At minimum prove:

```lean
theorem nonSevenPrimePowerSolubility_of_depthPacket
    ...
    (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerSolubilitySource p)
```

# Tests

Focused tests must cover:

- preservation of the generic diagonal counterexample from FLT7-015R;
- `q^e ∣ cell` and next-power nondivisibility;
- exact transfer to endpoint/root factors;
- units for nonaddressed outer factors;
- actual reduction to `ZMod (q^e)`;
- all three rows in each of the three columns;
- correction-unit proofs over a non-field prime-power modulus;
- full-depth classification from an abstract specialized depth packet.

Include at least one symbolic test with modulus `q^2` to ensure proofs do not
silently rely on field instances.

Avoid `native_decide`.

# Required report

Record:

- Outcome A/B/C;
- specialized address and exact exponent used;
- exact prime-power divisibility/maximality;
- unit facts for nonaddressed factors;
- actual full-depth reduction;
- normalized cubic-root extraction;
- prime-power Bezout/correction-unit result;
- all explicit soluble families;
- final full-depth classification;
- the distinction between single-prime full-depth solubility and simultaneous
  global signed reconstruction;
- recommended next boundary.

# Non-goals

Do not:

- assert generic prime-address uniqueness;
- modify or erase the FLT7-015 counterexample;
- use field-only arguments for `ZMod (q^e)`;
- claim simultaneous compatibility of different prime addresses;
- construct `AwayDescentClosureProvider` merely from local solutions;
- claim recursive descent or FLT7.

# Outcome classification

- Outcome A: actual specialized addresses and explicit families are soluble at
  their complete finite `q`-adic cell depth.
- Outcome B: actual reduction is complete, but explicit full-depth family
  classification needs a named follow-up.
- Outcome C: a specialized address fails to lift to its exact prime-power depth;
  provide a concrete arithmetic obstruction and preserve FLT7-015R.

Commit with a focused message and push to the current feature branch.
