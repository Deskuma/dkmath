# FLT7-013 — First-coordinate action on the cubic routing grid

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-012.

## Objective

Act on the explicit `3 × 3` prime-routing grid with the information that was
not used in FLT7-012:

1. the signed first-coordinate equation;
2. the four modulo-`7` endpoint sectors;
3. the exact first-coordinate remainders along the root factors
   `v`, `P(u,v)`, and `Q(u,v)`.

The checkpoint must prove two concrete layers.

First, localize the entire prime `7` support to exactly one pivot cell of the
routing grid, selected by the away residue sector:

```text
Y carrier:   pivot = c11
Z carrier:   pivot = c21
sum carrier: pivot = c31.
```

Second, attach a first-coordinate congruence to every routing cell. Every
nontrivial non-`7` cell must therefore produce an explicit finite-field local
solution of the corresponding endpoint/root polynomial system.

Attempt to eliminate all off-permutation cells or construct an
`AwayDescentClosureProvider`. If neither follows, stop with a strictly stronger
open object: the routing grid together with its pivot, signed data, all nine
first-coordinate constraints, and an exact non-`7` local-prime obstruction.

Do not repeat the FLT7-011 valuation proof.

## New modules

Create:

```text
DkMath/FLT/Seven/FirstCoordinateRemainders.lean
DkMath/FLT/Seven/RoutingSevenPivot.lean
DkMath/FLT/Seven/FirstCoordinateRoutingAudit.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenRoutingSevenPivot.lean
DkMathTest/FLT/SevenFirstCoordinateRoutingAudit.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-013.md
```

Suggested imports:

```lean
-- FirstCoordinateRemainders.lean
import DkMath.FLT.Seven.DescentClosureAudit

-- RoutingSevenPivot.lean
import DkMath.FLT.Seven.FirstCoordinateRemainders

-- FirstCoordinateRoutingAudit.lean
import DkMath.FLT.Seven.RoutingSevenPivot
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Endpoint first-coordinate remainders

Use the existing definition

```text
A(z,y) = cyclotomicSevenFst z y
       = z^3 + z^2*y - y^3.
```

Prove the two exact identities:

```lean
theorem cyclotomicSevenFst_sub_right_cube
    (z y : ℤ) :
    cyclotomicSevenFst z y - z ^ 3 =
      y * (z-y) * (z+y)
```

```lean
theorem cyclotomicSevenFst_add_left_cube
    (z y : ℤ) :
    cyclotomicSevenFst z y + y ^ 3 =
      z ^ 2 * (z+y)
```

Expose the corresponding divisibilities:

```lean
theorem leftEndpoint_dvd_fst_sub_right_cube
    (z y : ℤ) :
    y ∣ cyclotomicSevenFst z y - z ^ 3
```

```lean
theorem rightEndpoint_dvd_fst_add_left_cube
    (z y : ℤ) :
    z ∣ cyclotomicSevenFst z y + y ^ 3
```

```lean
theorem endpointSum_dvd_fst_add_left_cube
    (z y : ℤ) :
    z+y ∣ cyclotomicSevenFst z y + y ^ 3
```

The downstream row residues are therefore:

```text
row y:     A ≡ z^3,
row z:     A ≡ -y^3,
row y+z:   A ≡ -y^3.
```

# Part B — Root first-coordinate remainders

Retain the existing names

```text
F(u,v) = seventhPowerFst u v,
P(u,v) = seventhPowerSndLeftCubic u v,
Q(u,v) = seventhPowerSndRightCubic u v.
```

## B1. The `v` column

Define the degree-five remainder:

```lean
def seventhPowerFstVResidual (u v : ℤ) : ℤ :=
  -42 * u ^ 5
    - 70 * u ^ 4 * v
    + 70 * u ^ 3 * v ^ 2
    + 126 * u ^ 2 * v ^ 3
    + 14 * u * v ^ 4
    - 10 * v ^ 5
```

Prove:

```lean
theorem seventhPowerFst_eq_u_seven_add_v_sq
    (u v : ℤ) :
    seventhPowerFst u v =
      u ^ 7 + v ^ 2 * seventhPowerFstVResidual u v
```

Consequences:

```lean
theorem rootSnd_dvd_fst_sub_u_seven
    (u v : ℤ) :
    v ∣ seventhPowerFst u v - u ^ 7
```

```lean
theorem rootSnd_sq_dvd_fst_sub_u_seven
    (u v : ℤ) :
    v ^ 2 ∣ seventhPowerFst u v - u ^ 7
```

## B2. The `P` column

Define:

```lean
def leftFstQuotient (u v : ℤ) : ℤ :=
  u ^ 4 + 2 * u ^ 3 * v - 37 * u ^ 2 * v ^ 2
    - 143 * u * v ^ 3 - 255 * v ^ 4
```

```lean
def leftFstCorrection (u v : ℤ) : ℤ :=
  10 * u ^ 2 + 2 * u * v - 5 * v ^ 2
```

Prove the exact division identity:

```lean
theorem seventhPowerFst_leftCubic_division
    (u v : ℤ) :
    seventhPowerFst u v =
      seventhPowerSndLeftCubic u v * leftFstQuotient u v
        - 49 * v ^ 5 * leftFstCorrection u v
```

Expose:

```lean
theorem leftCubic_dvd_fst_add_correction
    (u v : ℤ) :
    seventhPowerSndLeftCubic u v ∣
      seventhPowerFst u v +
        49 * v ^ 5 * leftFstCorrection u v
```

## B3. The `Q` column

Define:

```lean
def rightFstQuotient (u v : ℤ) : ℤ :=
  u ^ 4 - 5 * u ^ 3 * v - 23 * u ^ 2 * v ^ 2
    + 74 * u * v ^ 3 - 157 * v ^ 4
```

```lean
def rightFstCorrection (u v : ℤ) : ℤ :=
  10 * u ^ 2 + 18 * u * v + 3 * v ^ 2
```

Prove:

```lean
theorem seventhPowerFst_rightCubic_division
    (u v : ℤ) :
    seventhPowerFst u v =
      seventhPowerSndRightCubic u v * rightFstQuotient u v
        + 49 * v ^ 5 * rightFstCorrection u v
```

Expose:

```lean
theorem rightCubic_dvd_fst_sub_correction
    (u v : ℤ) :
    seventhPowerSndRightCubic u v ∣
      seventhPowerFst u v -
        49 * v ^ 5 * rightFstCorrection u v
```

Prove these identities by `ring`; do not use polynomial division automation as
an unexposed oracle.

# Part C — Away root modulo-seven sector

Define the collapsed root coordinate:

```lean
def awayRootLinearModSeven
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) : ModSeven :=
  (p.root.fst : ModSeven) + 4 * (p.root.snd : ModSeven)
```

Package the three away sectors together with the root first coordinate.

```lean
inductive AwayRootResidueSector (x y z : ℕ)
    (p : AwayCoordinateNormalForm x y z) : Prop
  | yCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = 0)
      (hz : (z : ModSeven) = t)
      (hx : (x : ModSeven) = t)
      (hroot : awayRootLinearModSeven p = t ^ 3)
  | zCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = 0)
      (hx : (x : ModSeven) = -t)
      (hroot : awayRootLinearModSeven p = -t ^ 3)
  | sumCarrier (t : ModSeven) (ht : t ≠ 0)
      (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = -t)
      (hx : (x : ModSeven) = -2*t)
      (hroot : awayRootLinearModSeven p = -t ^ 3)
```

Prove:

```lean
theorem awayRootResidueSector_of_packet
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    AwayRootResidueSector x y z p
```

Use:

- `awayExceptionalFactor_of_packet`;
- `fermat7Equation_modSeven_linear`;
- `p.fst_eq`;
- `seventhPowerFst_mod_seven`;
- the endpoint first-coordinate remainder identities.

Do not enumerate residue triples.

Also prove:

```lean
theorem AwayCoordinateNormalForm.rootLinear_ne_zero
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    awayRootLinearModSeven p ≠ 0
```

This should agree with `root_norm_not_seven_dvd` and
`traceOneNorm_mod_seven_eq_linear_sq`.

# Part D — The unique seven-pivot cell

Use an `AwayCubicRoutingPacket` and its underlying
`AwayExceptionalCarrierSource`.

Define a sector-indexed pivot proposition. One acceptable form is:

```lean
inductive AwayRoutingSevenPivot
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Prop
  | rowY
      (h11 : 7 ∣ r.routing.c11)
      (h12 : ¬ 7 ∣ r.routing.c12)
      ...
      (h33 : ¬ 7 ∣ r.routing.c33)
  | rowZ
      (h21 : 7 ∣ r.routing.c21)
      ...
  | rowSum
      (h31 : 7 ∣ r.routing.c31)
      ...
```

Each constructor must assert that exactly its selected pivot is divisible by
`7` and the other eight cells are not.

Prove:

```lean
theorem awayRoutingSevenPivot_of_packet
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    AwayRoutingSevenPivot r
```

Proof architecture:

1. columns `P` and `Q` are not divisible by `7`, so none of their six cells is;
2. the one-hot exceptional endpoint source selects the only row divisible by
   `7`;
3. the other two cells of column `7*|v|` lie in nonexceptional rows;
4. primality of `7`, row products, and column products force the selected
   pivot cell to carry `7`.

Prove that the pivot carries all `7`-adic depth.

An acceptable structure is:

```lean
structure AwayRoutingPivotDepth
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  pivot : ℕ
  pivot_source :
    pivot = r.routing.c11 ∨
    pivot = r.routing.c21 ∨
    pivot = r.routing.c31
  carrier_eq :
    padicValNat 7 pivot =
      padicValNat 7 r.cubic.transfer.carrier
  root_eq :
    padicValNat 7 pivot =
      1 + padicValNat 7 r.cubic.rootTriple.vPart
```

Prove:

```lean
theorem nonempty_awayRoutingPivotDepth
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwayRoutingPivotDepth r)
```

This reuses FLT7-011; it does not reprove the transfer from scratch.

# Part E — Cell divisibility helpers

Provide a stable bridge from natural routing cells to signed integer
polynomials.

For example:

```lean
theorem intCast_dvd_of_dvd_natAbs
    {d : ℕ} {a : ℤ}
    (h : d ∣ Int.natAbs a) :
    (d : ℤ) ∣ a
```

and any converse needed locally.

Expose that each cell divides its row factor and column factor. The generic
routing structure only stores product equalities, so prove public helpers such
as:

```lean
theorem CoprimeTripleRouting.c11_dvd_row1 ...
theorem CoprimeTripleRouting.c11_dvd_col1 ...
```

A generic indexed `cell_dvd_row` / `cell_dvd_col` API is preferable if it stays
small. Otherwise explicit helpers for the nine cells are acceptable.

# Part F — First-coordinate constraints on the nine cells

Let

```text
u = root.fst,
v = root.snd,
A = cyclotomicSevenFst z y = seventhPowerFst u v.
```

For the `P` column, prove:

```lean
(r.c12 : ℤ) ∣
  (z : ℤ) ^ 3 + 49 * v ^ 5 * leftFstCorrection u v
```

```lean
(r.c22 : ℤ) ∣
  49 * v ^ 5 * leftFstCorrection u v - (y : ℤ) ^ 3
```

```lean
(r.c32 : ℤ) ∣
  49 * v ^ 5 * leftFstCorrection u v - (y : ℤ) ^ 3
```

For the `Q` column, prove:

```lean
(r.c13 : ℤ) ∣
  (z : ℤ) ^ 3 - 49 * v ^ 5 * rightFstCorrection u v
```

```lean
(r.c23 : ℤ) ∣
  (y : ℤ) ^ 3 + 49 * v ^ 5 * rightFstCorrection u v
```

```lean
(r.c33 : ℤ) ∣
  (y : ℤ) ^ 3 + 49 * v ^ 5 * rightFstCorrection u v
```

Here `r.cij` may require the full path `r.routing.cij`.

For the `7*|v|` column, use a prime-level statement because the pivot cell may
contain the distinguished factor `7` even when `7 ∤ v`.

Required pattern:

```lean
theorem prime_dvd_c11_firstCoordinate_constraint
    {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q)
    (hq7 : q ≠ 7)
    (hqc : q ∣ r.routing.c11) :
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 - (z : ℤ) ^ 3
```

The row-`z` and row-sum versions must conclude divisibility of

```text
u^7 + y^3.
```

Prove all three column-one statements uniformly if practical.

Package the complete surface:

```lean
structure AwayFirstCoordinateRoutingConstraints
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  rootSector : AwayRootResidueSector x y z r.cubic.transfer.normal
  sevenPivot : AwayRoutingSevenPivot r
  c12_constraint : ...
  c22_constraint : ...
  c32_constraint : ...
  c13_constraint : ...
  c23_constraint : ...
  c33_constraint : ...
  c11_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c11 → ...
  c21_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c21 → ...
  c31_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c31 → ...
```

Prove:

```lean
theorem nonempty_awayFirstCoordinateRoutingConstraints
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwayFirstCoordinateRoutingConstraints r)
```

# Part G — Extract explicit local-prime systems

Define row and column labels:

```lean
inductive EndpointRoutingRow
  | y | z | sum

inductive RootRoutingColumn
  | sevenV | leftCubic | rightCubic
```

Define a small record describing a nontrivial prime occurring in a cell:

```lean
structure AwayRoutingPrimeWitness
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r.routing row column
  endpoint_condition : Prop
  root_condition : Prop
  firstCoordinate_condition : Prop
  endpoint_condition_true : endpoint_condition
  root_condition_true : root_condition
  firstCoordinate_condition_true : firstCoordinate_condition
```

The three proposition fields may be replaced by constructor-specific indexed
witnesses. Prefer a representation in which the actual modular equations are
visible after case analysis.

Required extraction theorem:

```lean
theorem routingPrimeWitness_of_cell_ne_one
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (constraints : AwayFirstCoordinateRoutingConstraints r)
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
    (hcell : routingCell r.routing row column ≠ 1) :
    Nonempty (AwayRoutingPrimeWitness r)
```

Choose a prime divisor of the nontrivial cell and populate:

- the endpoint zero condition (`y=0`, `z=0`, or `y+z=0` in `ZMod q`);
- the root condition (`v=0`, `P=0`, or `Q=0` in `ZMod q`);
- the appropriate first-coordinate congruence from Part F;
- when `q=7`, prove that the witness is exactly the sector-selected pivot;
- when `q≠7`, retain the full local non-`7` system.

# Part H — Diagonalization / closure attempt

Define the desired strong outcomes separately.

```lean
structure AwayRoutingPermutationResolution
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  -- a permutation of the three columns assigned to the three rows
  permutation : Equiv.Perm (Fin 3)
  offPermutation_eq_one :
    ∀ i j, j ≠ permutation i → routingCellFin r.routing i j = 1
```

The exact finite-index API may be simplified, or replaced by six explicit
constructors. The distinguished `7` pivot must force the exceptional row to
map to the `sevenV` column, leaving only two possible assignments for `P,Q`.

Attempt one of the following:

1. prove a permutation resolution from the first-coordinate constraints;
2. construct `AwayDescentClosureProvider` directly;
3. prove that a permutation resolution plus an explicit signed compatibility
   condition constructs the closure provider.

A conditional bridge is required even if unconditional closure remains open:

```lean
theorem awayDescentClosureProvider_of_firstCoordinateResolution
    {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (resolution : AwayFirstCoordinateClosureResolution r) :
    Nonempty
      (AwayDescentClosureProvider x y z r.cubic.transfer)
```

Here `AwayFirstCoordinateClosureResolution` must contain the genuinely needed
reconstruction equations; do not define it as an alias for the desired
provider.

# Part I — Updated audit route

Define:

```lean
inductive FirstCoordinateClosureAuditResult
    (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayClosed
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (provider : AwayDescentClosureProvider x y z routing.cubic.transfer)
  | awayConstrained
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
```

Prove:

```lean
theorem firstCoordinateClosureAuditResult_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (FirstCoordinateClosureAuditResult x y z)
```

Use `awayConstrained` unless a provider has actually been constructed.

# Tests

Focused tests must cover abstract wiring only:

- both endpoint first-coordinate remainder identities;
- all three root division identities;
- construction of all three root residue sectors;
- all three possible `7` pivot positions;
- proof that the other eight cells are outside the `7` channel;
- pivot depth equals the exceptional carrier depth;
- the six full integer cell constraints for columns `P,Q`;
- the three prime-level non-`7` constraints for column `7*|v|`;
- extraction of local-prime witnesses from representative nontrivial cells;
- the conditional closure bridge;
- ramified and away-constrained audit routes.

Do not instantiate an actual counterexample.
Avoid `native_decide`.

# Required report

Record:

- exact definition/theorem/structure surface;
- the endpoint and root first-coordinate division identities;
- the root modulo-seven sector;
- the unique `7` pivot cell and its exact depth;
- all nine first-coordinate routing constraints;
- the extracted local-prime systems;
- which off-permutation cells were eliminated, if any;
- whether an unconditional closure provider was constructed;
- the exact remaining non-`7` local obstruction if closure remains open;
- recommended FLT7-014 boundary.

The report must distinguish:

```text
7-primary routing: completely localized
```

from

```text
non-7 prime routing: eliminated, resolved, or still open.
```

If closure remains open, FLT7-014 should classify the finite-field local-prime
systems by column (`v`, `P`, `Q`) and row (`y`, `z`, `y+z`), using resultants or
proved residue-class restrictions. Do not repeat the routing construction.

# Non-goals

Do not add:

- an FLT7 contradiction without a constructed recursive packet;
- a fabricated `AwayDescentClosureProvider`;
- a claim that pairwise-coprime product equality forces a permutation;
- a repeated proof of the FLT7-011 valuation transfer;
- general cyclotomic ideal theory;
- unrestricted computer enumeration;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: the first-coordinate constraints eliminate enough routing to
  construct an unconditional `AwayDescentClosureProvider`.
- Outcome B: the unique `7` pivot and all nine first-coordinate local systems
  are complete, but one or more non-`7` routing systems remain open; expose
  them exactly and update the audit route.
- Outcome C: one of the proposed exact polynomial identities is false; report
  the concrete identity failure and preserve FLT7-012.

Commit with a focused message and push to the current feature branch.
