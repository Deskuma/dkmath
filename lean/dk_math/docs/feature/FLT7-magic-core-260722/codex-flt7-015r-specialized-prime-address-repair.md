# FLT7-015R — Specialized prime-address repair

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after the honest FLT7-015 Outcome C audit.

## Status to preserve

FLT7-014 remains unchanged.

The generic statement

```text
prime_dvd_two_routingCells_implies_eq
```

for an arbitrary `CoprimeTripleRouting` is false. Keep
`report-flt7-015.md` as the permanent counterexample record. Do not weaken,
hide, or overwrite that audit.

The repair must be specialized to `AwayCubicRoutingPacket`, whose outer
endpoint and root factors are pairwise coprime.

## Objective

Prove that a nontrivial prime has a unique routing-cell address inside an
actual FLT7 away routing packet, using the outer factor provenance:

```text
endpoint rows: y, z, y+z
root columns:  7*vPart, leftPart, rightPart.
```

Then recover exact cell/row/column valuation isolation on this corrected
surface.

This checkpoint repairs the address foundation only. Do not yet construct the
`ZMod (q^e)` solubility layer.

## New module and tests

Create:

```text
DkMath/FLT/Seven/SpecializedPrimeAddress.lean
DkMathTest/FLT/SevenSpecializedPrimeAddress.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-015r.md
```

Suggested import:

```lean
import DkMath.FLT.Seven.LocalObstructionAudit
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Expose outer row and column coprimality

For endpoint rows, prove stable pairwise accessors:

```lean
theorem AwayCubicRoutingPacket.endpoint_y_z_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime y z
```

```lean
theorem AwayCubicRoutingPacket.endpoint_y_sum_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime y (y+z)
```

```lean
theorem AwayCubicRoutingPacket.endpoint_z_sum_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime z (y+z)
```

These should reuse `r.cubic.endpointTriple`.

For root columns, expose:

```lean
theorem AwayCubicRoutingPacket.column_sevenV_left_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime
      (7 * r.cubic.rootTriple.vPart)
      r.cubic.rootTriple.leftPart
```

```lean
theorem AwayCubicRoutingPacket.column_sevenV_right_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime
      (7 * r.cubic.rootTriple.vPart)
      r.cubic.rootTriple.rightPart
```

```lean
theorem AwayCubicRoutingPacket.column_left_right_coprime
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime
      r.cubic.rootTriple.leftPart
      r.cubic.rootTriple.rightPart
```

The last theorem is already in `rootTriple`. For the first two, reuse the
existing facts that `7` divides neither cubic part and combine them with
`coprime_v_left` / `coprime_v_right` exactly as done in
`nonempty_awayCubicRoutingPacket`.

Do not add these invariants to generic `CoprimeTripleRouting`.

# Part B — Row and column factor selectors

Define natural-valued selectors matching the routing grid:

```lean
def endpointRoutingFactorNat (y z : ℕ) : EndpointRoutingRow → ℕ
  | .y => y
  | .z => z
  | .sum => y+z
```

```lean
def rootRoutingFactorNat {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : RootRoutingColumn → ℕ
  | .sevenV => 7 * r.cubic.rootTriple.vPart
  | .leftCubic => r.cubic.rootTriple.leftPart
  | .rightCubic => r.cubic.rootTriple.rightPart
```

Prove or reuse:

```lean
routingCell r.routing row column ∣ endpointRoutingFactorNat y z row
```

```lean
routingCell r.routing row column ∣ rootRoutingFactorNat r column
```

# Part C — Outer prime-support uniqueness

Prove row uniqueness from endpoint outer coprimality:

```lean
theorem AwayCubicRoutingPacket.row_eq_of_prime_dvd_cells
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow}
    {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) :
    row₁ = row₂
```

Proof architecture:

1. each cell divides its endpoint row factor;
2. if rows differ, `q` divides two distinct members of the pairwise-coprime
   endpoint triple;
3. `Nat.eq_one_of_dvd_coprimes` gives `q=1`, contradicting `hq.ne_one`.

Prove column uniqueness independently from root outer coprimality:

```lean
theorem AwayCubicRoutingPacket.column_eq_of_prime_dvd_cells
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow}
    {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) :
    column₁ = column₂
```

Then prove the corrected address theorem:

```lean
theorem AwayCubicRoutingPacket.prime_address_unique
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow}
    {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) :
    row₁ = row₂ ∧ column₁ = column₂
```

This theorem must mention `AwayCubicRoutingPacket` explicitly. No generic alias
or hidden typeclass should make it appear valid for arbitrary routing grids.

# Part D — Stable specialized address packet

Define:

```lean
structure AwayRoutingPrimeAddress {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r.routing row column
  unique : ∀ row' column',
    q ∣ routingCell r.routing row' column' →
    row' = row ∧ column' = column
```

Construct it from any prime divisor of a nontrivial cell:

```lean
theorem nonempty_awayRoutingPrimeAddress_of_cell_ne_one
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z)
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (hcell : routingCell r.routing row column ≠ 1) :
    Nonempty (AwayRoutingPrimeAddress r)
```

Use `Nat.exists_prime_and_dvd` and the corrected specialized uniqueness theorem.

# Part E — Exact specialized valuation isolation

For a fixed address `a`, prove all other cells in the same endpoint row and all
other cells in the same root column are not divisible by `a.q`. The global
uniqueness theorem may be used directly.

Expose exact depth equality:

```lean
theorem AwayRoutingPrimeAddress.cell_depth_eq_endpoint_depth
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (endpointRoutingFactorNat y z a.row)
```

```lean
theorem AwayRoutingPrimeAddress.cell_depth_eq_root_depth
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (rootRoutingFactorNat r a.column)
```

Use the row/column product equations and `padicValNat.mul`; the other two cells
have valuation zero by uniqueness. Handle nonzero obligations from positivity
of the endpoint/root triples and `a.q_dvd_cell`.

Package:

```lean
structure AwayRoutingPrimeDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  address : AwayRoutingPrimeAddress r
  exponent : ℕ
  exponent_eq_cell : exponent =
    padicValNat address.q
      (routingCell r.routing address.row address.column)
  exponent_pos : 0 < exponent
  endpoint_depth_eq :
    padicValNat address.q
      (endpointRoutingFactorNat y z address.row) = exponent
  root_depth_eq :
    padicValNat address.q
      (rootRoutingFactorNat r address.column) = exponent
```

Construct this from an address.

# Part F — Regression tests

Focused tests must include:

1. a direct construction of the FLT7-015 generic counterexample grid
   `c11=2,c22=2,others=1`, demonstrating only that it inhabits
   `CoprimeTripleRouting 2 2 1 2 2 1`;
2. no theorem claiming generic prime-address uniqueness;
3. abstract specialized row uniqueness;
4. abstract specialized column uniqueness;
5. full specialized address uniqueness;
6. exact cell/endpoint/root depth equalities.

The counterexample test is a permanent regression guard against accidentally
reintroducing the false abstraction.

# Required report

Record:

- Outcome A/B/C;
- the preserved generic counterexample;
- why outer endpoint coprimality repairs row uniqueness;
- why outer root coprimality repairs column uniqueness;
- the exact specialized theorem surface;
- the valuation-isolation packet;
- verification and axiom audit;
- recommended next boundary.

The recommended next boundary may resume the `ZMod (q^e)` actual-cell and
explicit-solubility audit, but only through `AwayRoutingPrimeDepthPacket`.

# Non-goals

Do not:

- alter FLT7-014;
- delete or rewrite `report-flt7-015.md`;
- prove generic address uniqueness for `CoprimeTripleRouting`;
- strengthen the generic structure unless independently justified by all users;
- construct prime-power local solutions in this repair checkpoint;
- claim recursive closure, descent, or FLT7.

# Outcome classification

- Outcome A: specialized address uniqueness and exact valuation isolation are
  complete.
- Outcome B: specialized address uniqueness is complete, but valuation
  isolation needs a named follow-up.
- Outcome C: even the specialized theorem is false; provide a concrete
  `AwayCubicRoutingPacket` counterexample and preserve all prior work.

Commit with a focused message and push to the current feature branch.
