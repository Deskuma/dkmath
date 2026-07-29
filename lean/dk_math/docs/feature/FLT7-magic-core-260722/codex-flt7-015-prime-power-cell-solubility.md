# FLT7-015 — Exact prime-power cell support and finite q-adic solubility

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-014.

## Objective

Move from first-residue solubility to the exact prime-power depth carried by a
routing cell.

For every prime `q != 7` occurring in the away routing grid:

1. prove that `q` occurs in exactly one of the nine cells;
2. prove that the `q`-adic depth of that cell equals the depth of its endpoint
   row factor and root column factor;
3. let `e` be this exact positive depth;
4. reduce the actual integer endpoint/root/first-coordinate data modulo `q^e`;
5. prove that the resulting full-depth local system is soluble;
6. classify the full-depth solution into the same three explicit families as
   FLT7-014: `sevenV`, left cubic, or right cubic.

The intended conclusion is:

```text
No single non-seven prime, no single routing cell, and no finite q-adic depth
of that cell is an obstruction.
```

This does not construct the missing global signed reconstruction or a new
`CounterexamplePack`. The remaining obstruction must be simultaneous gluing
across all prime-addressed cells.

## New modules

Create:

```text
DkMath/FLT/Seven/RoutingPrimeAddress.lean
DkMath/FLT/Seven/RoutingPrimePowerSystems.lean
DkMath/FLT/Seven/RoutingPrimePowerSolubility.lean
DkMath/FLT/Seven/PrimePowerLocalAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenRoutingPrimeAddress.lean
DkMathTest/FLT/SevenRoutingPrimePowerSolubility.lean
DkMathTest/FLT/SevenPrimePowerLocalAudit.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-015.md
```

Suggested imports:

```lean
-- RoutingPrimeAddress.lean
import DkMath.FLT.Seven.LocalObstructionAudit

-- RoutingPrimePowerSystems.lean
import DkMath.FLT.Seven.RoutingPrimeAddress

-- RoutingPrimePowerSolubility.lean
import DkMath.FLT.Seven.RoutingPrimePowerSystems

-- PrimePowerLocalAudit.lean
import DkMath.FLT.Seven.RoutingPrimePowerSolubility
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — A prime has one global cell address

The routing rows and columns are pairwise coprime. Strengthen the existing
row/column disjointness to global cell uniqueness.

Required theorem shape:

```lean
theorem prime_dvd_two_routingCells_implies_eq
    {a₁ a₂ a₃ b₁ b₂ b₃ q : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃)
    (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow}
    {col₁ col₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r row₁ col₁)
    (h₂ : q ∣ routingCell r row₂ col₂) :
    row₁ = row₂ ∧ col₁ = col₂
```

Proof architecture:

- if the rows differ, `q` divides two pairwise-coprime endpoint factors;
- if the columns differ, `q` divides two pairwise-coprime root factors;
- primality excludes both possibilities.

Define a stable address packet:

```lean
structure RoutingPrimeAddress
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃)
    (q : ℕ) : Type where
  q_prime : Nat.Prime q
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r row column
  unique : ∀ row' column',
    q ∣ routingCell r row' column' → row' = row ∧ column' = column
```

Prove construction from any prime divisor of the total product or any
`AwayRoutingPrimeWitness`.

Recommended public constructors:

```lean
routingPrimeAddress_of_cell
routingPrimeAddress_of_primeWitness
```

# Part B — Exact valuation is isolated in the addressed cell

Add accessors for the natural endpoint row factor and root column factor.
Reuse the current integer-valued labels only where needed; the valuation layer
should use naturals.

Suggested definitions:

```lean
def endpointRoutingFactorNat (y z : ℕ) : EndpointRoutingRow → ℕ
  | .y => y
  | .z => z
  | .sum => y+z


def rootRoutingFactorNat {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : RootRoutingColumn → ℕ
  | .sevenV => 7 * r.cubic.rootTriple.vPart
  | .leftCubic => r.cubic.rootTriple.leftPart
  | .rightCubic => r.cubic.rootTriple.rightPart
```

For an addressed prime, prove all other cells in its row and column have
valuation zero, then prove:

```lean
theorem routingPrimeAddress_cell_depth_eq_row_depth ... :
  padicValNat q (routingCell r row column) =
    padicValNat q (endpointRoutingFactorNat ... row)
```

```lean
theorem routingPrimeAddress_cell_depth_eq_column_depth ... :
  padicValNat q (routingCell r row column) =
    padicValNat q (rootRoutingFactorNat ... column)
```

Package the exact exponent:

```lean
structure AwayRoutingPrimePowerWitness {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  q_ne_seven : q ≠ 7
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r.routing row column
  exponent : ℕ
  exponent_eq : exponent = padicValNat q (routingCell r.routing row column)
  exponent_pos : 0 < exponent
  q_pow_dvd_cell : q ^ exponent ∣ routingCell r.routing row column
  q_succ_pow_not_dvd_cell :
    ¬ q ^ (exponent + 1) ∣ routingCell r.routing row column
  row_depth_eq :
    padicValNat q (endpointRoutingFactorNat y z row) = exponent
  column_depth_eq :
    padicValNat q (rootRoutingFactorNat r column) = exponent
```

Field orientation may be adjusted, but preserve exact depth and provenance.

Prove:

```lean
nonempty_primePowerWitness_of_primeWitness
primePowerWitness_of_primeWitness
```

Use the existing `AwayRoutingPrimeWitness`; do not select a second unrelated
prime or cell.

# Part C — Prime-power local-system surface

Reuse the FLT7-014 equations with modulus `q^e`:

```text
AwayEndpointLocalEquation
AwayEndpointLocalNondegenerate
AwayRootLocalEquation
AwayRootLocalNondegenerate
AwayFirstCoordinateLocalEquation
```

They are already generic in the `ZMod` modulus and should not be duplicated.

Define only a metadata wrapper:

```lean
abbrev PrimePowerModulus (q e : ℕ) := q ^ e

structure AwayRoutingPrimePowerSolution
    (q e : ℕ)
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn) : Type where
  exponent_pos : 0 < e
  solution : AwayRoutingLocalSolution (q ^ e) row column
```

An equivalent abbreviation plus separate positivity theorem is acceptable.

# Part D — The actual cell gives a solution at its full exponent

For `w : AwayRoutingPrimePowerWitness r`, prove that the original integer
coordinates reduce to a solution modulo `w.q ^ w.exponent`.

Required theorem:

```lean
noncomputable def AwayRoutingPrimePowerWitness.toPrimePowerLocalSolution
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimePowerWitness r) :
    AwayRoutingPrimePowerSolution w.q w.exponent w.row w.column
```

Architecture:

- `q^e ∣ cell` and `cell ∣ endpoint factor` give the endpoint equation;
- the same cell-to-column divisibility gives the root equation;
- the FLT7-013 first-coordinate constraint is divisible by the cell, hence by
  `q^e`;
- row/column pairwise coprimality proves the required nonzero coordinates
  modulo `q^e`;
- in the `sevenV` column, use root-coordinate coprimality to show `u` remains
  nonzero;
- in cubic columns, `q ∤ v`, hence `v` remains nonzero modulo `q^e`.

Do not weaken this theorem to modulus `q`.

# Part E — Units modulo q^e

Prove the arithmetic unit layer for `q` prime, `q != 7`, `e > 0`.

Required facts:

```lean
theorem seven_isUnit_zmod_primePower ... : IsUnit (7 : ZMod (q^e))
theorem fortyNine_isUnit_zmod_primePower ... : IsUnit (49 : ZMod (q^e))
```

If `a : ℤ` is not divisible by `q`, expose a helper proving its cast is a unit
modulo `q^e`.

Use coprimality with `q^e`; do not enumerate residues.

# Part F — Homogeneous Bezout certificates at prime-power depth

The normalized certificates from FLT7-014 have right side `7`. They therefore
remain valid modulo `q^e` and show the correction is a unit, not merely nonzero.

Required theorems:

```lean
theorem leftCorrection_isUnit_of_leftCubic_eq_zero_primePower
    {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (t : ZMod (q^e))
    (hP : leftCubicNormalizedZMod t = 0) :
    IsUnit (leftCorrectionNormalizedZMod t)
```

```lean
theorem rightCorrection_isUnit_of_rightCubic_eq_zero_primePower ...
```

Also expose the homogeneous integer identities:

```text
(60u-88v) P(u,v)
  + (-6u^2+22uv-19v^2) L(u,v) = 7 v^4,

(60u+148v) Q(u,v)
  + (-6u^2-34uv-47v^2) R(u,v) = 7 v^4.
```

Suggested theorem names:

```lean
left_cubic_correction_homogeneous_bezout
right_cubic_correction_homogeneous_bezout
```

These identities should also prove directly that, when `v` is a unit and the
cubic vanishes modulo `q^e`, the corresponding homogeneous correction is a
unit.

# Part G — Parametric solutions over every q^e

Generalize the FLT7-014 scale construction from a field `ZMod q` to the ring
`ZMod (q^e)`.

The polynomial identities themselves use only commutative-ring algebra. The
nondegeneracy proofs should use units.

Required constructors:

```lean
theorem nonempty_primePowerLocalSolution_sevenV
    {q e : ℕ} (hq : Nat.Prime q) (he : 0 < e)
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingPrimePowerSolution q e row .sevenV)
```

```lean
theorem nonempty_primePowerLocalSolution_leftCubic_of_root
    {q e : ℕ} (hq : Nat.Prime q) (hq7 : q ≠ 7) (he : 0 < e)
    (t : ZMod (q^e))
    (hroot : leftCubicNormalizedZMod t = 0)
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingPrimePowerSolution q e row .leftCubic)
```

```lean
theorem nonempty_primePowerLocalSolution_rightCubic_of_root ...
```

Use exactly the same signed scales as FLT7-014:

```text
left/Y:    C = -49 L(t)
left/Z:    C =  49 L(t)
left/Sum:  C =  49 L(t)

right/Y:   C =  49 R(t)
right/Z:   C = -49 R(t)
right/Sum: C = -49 R(t)
```

and

```text
v = C^2,
u = t*C^2,
endpoint magnitude = C^5.
```

Because `49` and the correction are units, `C` is a unit and every required
nonzero condition follows.

# Part H — Extract the normalized root from an actual full-depth witness

For cubic columns, prove `v` is a unit modulo `q^e`, define the normalized root

```text
t = u / v
```

using a unit inverse, and prove the corresponding normalized cubic equation.

Recommended theorems:

```lean
AwayRoutingPrimePowerWitness.rootSnd_isUnit
AwayRoutingPrimePowerWitness.left_normalized_root
AwayRoutingPrimePowerWitness.right_normalized_root
```

The theorem may return a dependent package:

```lean
∃ t : ZMod (q^e),
  leftCubicNormalizedZMod t = 0
```

or the right-cubic analogue.

Do not assume `ZMod (q^e)` is a field.

# Part I — Full-depth family classification

Define:

```lean
inductive AwayNonSevenPrimePowerSolubilitySource
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimePowerWitness r) : Type
  | sevenV
      (family : Nonempty
        (AwayRoutingPrimePowerSolution w.q w.exponent w.row .sevenV))
  | leftCubic
      (t : ZMod (w.q ^ w.exponent))
      (root_eq : leftCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (leftCorrectionNormalizedZMod t))
      (family : Nonempty
        (AwayRoutingPrimePowerSolution w.q w.exponent w.row .leftCubic))
  | rightCubic
      (t : ZMod (w.q ^ w.exponent))
      (root_eq : rightCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (rightCorrectionNormalizedZMod t))
      (family : Nonempty
        (AwayRoutingPrimePowerSolution w.q w.exponent w.row .rightCubic))
```

Prove:

```lean
theorem primePowerSolubilitySource_of_witness
    (w : AwayRoutingPrimePowerWitness r) :
    Nonempty (AwayNonSevenPrimePowerSolubilitySource w)
```

This must classify the witness at its exact cell exponent, not at exponent one.

# Part J — Audit packet and summit

Define an away audit package retaining the FLT7-013 routing and constraints:

```lean
structure AwayPrimePowerLocalAudit (x y z : ℕ) : Type where
  routing : AwayCubicRoutingPacket x y z
  constraints : AwayFirstCoordinateRoutingConstraints routing
  classify : ∀ row column,
    routingCell routing.routing row column ≠ 1 →
    ∀ q, Nat.Prime q → q ≠ 7 →
      q ∣ routingCell routing.routing row column →
      ∃ w : AwayRoutingPrimePowerWitness routing,
        w.q = q ∧ w.row = row ∧ w.column = column ∧
        Nonempty (AwayNonSevenPrimePowerSolubilitySource w)
```

An equivalent dependent formulation is acceptable.

Define the final route:

```lean
inductive PrimePowerLocalAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayPrimePowerSoluble (audit : AwayPrimePowerLocalAudit x y z)
```

Prove:

```lean
theorem primePowerLocalAuditResult_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (PrimePowerLocalAuditResult x y z)
```

# Part K — Explicit remaining global obligation

Do not end with only prose. Define the next missing provider as a type.

One acceptable boundary type is:

```lean
structure AwayGlobalSignedRoutingReconstruction
    (x y z : ℕ) (audit : AwayPrimePowerLocalAudit x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  signedCarrierCompatibility :
    nextRoute.carrier = Int.natAbs audit.routing.cubic.transfer.normal.root.snd
  globalCellCompatibility : Prop
```

Do not insert an arbitrary unproved proposition as evidence. The final field
may instead be replaced by concrete signed row/column reconstruction equations
if they can be identified during implementation. The purpose is to expose that
all single-cell prime-power systems are soluble while simultaneous global
integer gluing remains open.

# Tests

Focused tests must cover abstract wiring only:

- uniqueness of a prime cell address;
- exact cell/row/column valuation equality;
- exact exponent and next-power nondivisibility;
- reduction of an actual cell to `ZMod (q^e)`;
- unit status of `7`, `49`, and cubic corrections modulo `q^e`;
- both homogeneous Bezout identities;
- all nine prime-power parametric solution constructors;
- normalized-root extraction without a field instance;
- classification of each root column at exact exponent;
- construction of the final audit route.

Do not instantiate an actual counterexample.
Avoid `native_decide`.

# Required report

Record:

- exact theorem/definition/structure surface;
- global uniqueness of each prime's routing address;
- exact equality of cell, row, and column valuations;
- the full-depth witness construction at `q^e`;
- unit proofs in `ZMod (q^e)`;
- homogeneous Bezout certificates;
- prime-power versions of all nine explicit solution families;
- normalized-root extraction from an actual cell;
- full-depth family classification;
- final audit route;
- the exact remaining global signed-gluing provider;
- recommended FLT7-016 boundary.

The report must state clearly whether the result proves:

```text
all finite single-cell q-adic layers are soluble
```

or whether a genuine prime-power obstruction appears.

If all are soluble, the recommended FLT7-016 boundary is the simultaneous
global cell-gluing problem: reconstruct signed integer row and column factors
from all prime addresses at once and combine them with the first-coordinate
integer equality. Do not repeat a local residue or prime-power audit.

# Non-goals

Do not add:

- an unconditional global reconstruction;
- a recursive descent theorem;
- an FLT7 contradiction or no-solution theorem;
- p-adic completions or infinite Hensel theory;
- residue enumeration;
- a general theorem for arbitrary routing dimensions;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: prime addresses and exact exponents are isolated, and every actual
  non-seven cell is classified into an explicit soluble family over its full
  modulus `q^e`; no finite single-cell q-adic obstruction remains.
- Outcome B: exact prime-power witnesses are constructed, but one or more
  columns exhibit a genuine lifting obstruction or the explicit family cannot
  be extended beyond exponent one. Report the exact cell, prime, exponent, and
  failed equation.
- Outcome C: the proposed exact valuation/address theorem is false; report an
  explicit routing counterexample and preserve FLT7-014.

Commit with a focused message and push to the current feature branch.
