# FLT7-014 — Classification and solubility audit of the nine non-seven local systems

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-013.

## Objective

Classify the nine finite-field systems exposed by FLT7-013.

Do not assume that a local system is obstructed merely because it contains a
cubic root equation and a first-coordinate equation. Audit actual solubility.

The expected arithmetic is:

```text
sevenV column:
  all three row systems have explicit nonzero parametric solutions;

leftCubic/rightCubic columns:
  the correction is nonzero at every cubic root for q != 7,
  and all six row systems have explicit nonzero solutions conditional on the
  corresponding cubic root.
```

Thus the first residue layer may prove insufficient to eliminate non-seven
routing. If this expected classification is correct, formalize that fact
explicitly instead of continuing to search for a contradiction in a locally
soluble system.

This checkpoint must not claim recursive closure, descent, or FLT7.

## New modules

Create:

```text
DkMath/FLT/Seven/RoutingLocalSystems.lean
DkMath/FLT/Seven/RoutingLocalSolubility.lean
DkMath/FLT/Seven/LocalObstructionAudit.lean
```

Suggested imports:

```lean
-- RoutingLocalSystems.lean
import DkMath.FLT.Seven.FirstCoordinateRoutingAudit

-- RoutingLocalSolubility.lean
import DkMath.FLT.Seven.RoutingLocalSystems

-- LocalObstructionAudit.lean
import DkMath.FLT.Seven.RoutingLocalSolubility
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenRoutingLocalSystems.lean
DkMathTest/FLT/SevenLocalObstructionAudit.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-014.md
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Stable normalized polynomials

Define the dehomogenized cubic and correction polynomials:

```lean
def leftCubicNormalized (t : ℤ) : ℤ :=
  t^3 - 2*t^2 - t + 1

def rightCubicNormalized (t : ℤ) : ℤ :=
  t^3 + 5*t^2 + 6*t + 1

def leftCorrectionNormalized (t : ℤ) : ℤ :=
  10*t^2 + 2*t - 5

def rightCorrectionNormalized (t : ℤ) : ℤ :=
  10*t^2 + 18*t + 3
```

Prove the homogenization identities:

```lean
theorem leftCubic_scale (t s : ℤ) :
  seventhPowerSndLeftCubic (t*s) s = s^3 * leftCubicNormalized t

theorem rightCubic_scale (t s : ℤ) :
  seventhPowerSndRightCubic (t*s) s = s^3 * rightCubicNormalized t

theorem leftCorrection_scale (t s : ℤ) :
  leftFstCorrection (t*s) s = s^2 * leftCorrectionNormalized t

theorem rightCorrection_scale (t s : ℤ) :
  rightFstCorrection (t*s) s = s^2 * rightCorrectionNormalized t
```

Prove the involutive relation between the two cubic columns:

```lean
theorem rightCubicNormalized_eq_left_transform (t : ℤ) :
  rightCubicNormalized t = -leftCubicNormalized (-t-1)

theorem rightCorrectionNormalized_eq_left_transform (t : ℤ) :
  rightCorrectionNormalized t = leftCorrectionNormalized (-t-1)
```

These identities should also be exposed after coercion to `ZMod q` through
small helper lemmas if that improves downstream rewriting.

# Part B — Exact resultant/Bezout certificates

Prove the integral polynomial identities:

```lean
theorem left_cubic_correction_bezout (t : ℤ) :
  (60*t - 88) * leftCubicNormalized t +
    (-6*t^2 + 22*t - 19) * leftCorrectionNormalized t = 7
```

```lean
theorem right_cubic_correction_bezout (t : ℤ) :
  (60*t + 148) * rightCubicNormalized t +
    (-6*t^2 - 34*t - 47) * rightCorrectionNormalized t = 7
```

These are explicit certificates of

```text
Res(left cubic, left correction) = 7,
Res(right cubic, right correction) = 7.
```

No generic resultant library is required; the displayed identities proved by
`ring` are the public trusted surface.

For a prime `q != 7`, prove the finite-field consequences:

```lean
theorem leftCorrection_ne_zero_of_leftCubic_eq_zero
    {q : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) (t : ZMod q)
    (hP : leftCubicNormalizedZMod t = 0) :
    leftCorrectionNormalizedZMod t ≠ 0
```

```lean
theorem rightCorrection_ne_zero_of_rightCubic_eq_zero
    {q : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) (t : ZMod q)
    (hQ : rightCubicNormalizedZMod t = 0) :
    rightCorrectionNormalizedZMod t ≠ 0
```

Choose clear names for the `ZMod` polynomial versions. Avoid repeated casts in
the proof surface.

# Part C — A typed local system

Define predicates for the three endpoint rows:

```text
Y row:     y = 0, z != 0
Z row:     z = 0, y != 0
sum row:   y+z = 0, y != 0, z != 0
```

Define predicates for the three root columns:

```text
sevenV:       v = 0, u != 0
leftCubic:    P(u,v) = 0, v != 0
rightCubic:   Q(u,v) = 0, v != 0
```

Use the exact first-coordinate values from
`routingFirstCoordinateValue` but formulate them directly in `ZMod q`.

One acceptable structure is:

```lean
structure AwayRoutingLocalSolution
    (q : ℕ) [Fact (Nat.Prime q)]
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn) : Type where
  u : ZMod q
  v : ZMod q
  y : ZMod q
  z : ZMod q
  endpoint_nonzero : AwayEndpointLocalNondegenerate row y z
  endpoint_equation : AwayEndpointLocalEquation row y z
  root_nonzero : AwayRootLocalNondegenerate column u v
  root_equation : AwayRootLocalEquation column u v
  first_coordinate_equation :
    AwayFirstCoordinateLocalEquation row column u v y z
```

The exact predicate names and decomposition may be improved. The important
point is that the same structure represents all nine systems without erasing
row/column provenance.

Prove conversion from an actual FLT7-013 witness:

```lean
theorem AwayRoutingPrimeWitness.toLocalSolution
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimeWitness r)
    (hq7 : w.q ≠ 7) :
    AwayRoutingLocalSolution w.q w.row w.column
```

This theorem should use the actual endpoint/root values reduced modulo `q`.
It is a grounding theorem, not the solubility classification itself.

# Part D — Universal solubility of the sevenV column

For every prime `q`, every row in the `sevenV` column has an explicit nonzero
solution.

Use a nonzero scale `s : ZMod q`.

Y row:

```text
u = s^3,
v = 0,
y = 0,
z = s^7.
```

Then `u^7 = z^3`.

Z row:

```text
u = -s^3,
v = 0,
y = s^7,
z = 0.
```

Then `u^7 + y^3 = 0`.

Sum row:

```text
u = -s^3,
v = 0,
y = s^7,
z = -s^7.
```

Again `u^7 + y^3 = 0`.

Required surface may be either three theorems or one row-generic theorem:

```lean
theorem nonempty_localSolution_sevenV
    {q : ℕ} [Fact (Nat.Prime q)]
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .sevenV)
```

When `q=2`, verify all nonzero conditions explicitly; do not silently use
`-s != 0` without a field argument.

# Part E — Parametric solubility of the left cubic column

Let `t : ZMod q` satisfy the normalized left cubic equation. For `q != 7`, put

```text
L = leftCorrectionNormalizedZMod t.
```

Part B proves `L != 0`.

For each row choose a signed constant `C`:

```text
Y row:     C = -49*L
Z row:     C =  49*L
sum row:   C =  49*L
```

Then define

```text
v = C^2,
u = t*C^2.
```

Endpoint values:

```text
Y row:     y = 0,   z = C^5
Z row:     y = C^5, z = 0
sum row:   y = C^5, z = -C^5.
```

Use homogenization and

```text
(C^5)^3 = C * (C^2)^7
```

to prove the first-coordinate equation.

Required theorem:

```lean
theorem nonempty_localSolution_leftCubic_of_root
    {q : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7)
    (t : ZMod q)
    (hroot : leftCubicNormalizedZMod t = 0)
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .leftCubic)
```

All endpoint and root nonzero facts must be proved from `C != 0`.

# Part F — Parametric solubility of the right cubic column

Mirror Part E using

```text
R = rightCorrectionNormalizedZMod t.
```

Signed constants:

```text
Y row:     C =  49*R
Z row:     C = -49*R
sum row:   C = -49*R.
```

Use the same scale pattern:

```text
v = C^2,
u = t*C^2,
endpoint magnitude = C^5.
```

Required theorem:

```lean
theorem nonempty_localSolution_rightCubic_of_root
    {q : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7)
    (t : ZMod q)
    (hroot : rightCubicNormalizedZMod t = 0)
    (row : EndpointRoutingRow) :
    Nonempty (AwayRoutingLocalSolution q row .rightCubic)
```

Where useful, derive this theorem through the involution `t -> -t-1` rather
than duplicating all algebra. Preserve clear row signs in the public theorem.

# Part G — Classification of actual non-seven witnesses

Define a classification certificate:

```lean
inductive AwayNonSevenLocalSolubilitySource
    (q : ℕ) [Fact (Nat.Prime q)]
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn) : Type
  | sevenV
      (solution : AwayRoutingLocalSolution q row .sevenV)
  | leftCubic
      (t : ZMod q)
      (root : leftCubicNormalizedZMod t = 0)
      (solution : AwayRoutingLocalSolution q row .leftCubic)
  | rightCubic
      (t : ZMod q)
      (root : rightCubicNormalizedZMod t = 0)
      (solution : AwayRoutingLocalSolution q row .rightCubic)
```

Equivalent indexing is acceptable.

For an actual non-seven prime witness, extract the normalized cubic root in the
`P,Q` columns by dividing `u` by nonzero `v`. Then prove:

```lean
theorem localSolubilitySource_of_primeWitness
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (w : AwayRoutingPrimeWitness r)
    (hq7 : w.q ≠ 7) :
    Nonempty
      (AwayNonSevenLocalSolubilitySource w.q w.row w.column)
```

This theorem certifies that every non-seven witness belongs to one of the
explicitly soluble model families.

# Part H — Honest obstruction audit

Define:

```lean
inductive FirstResidueLocalAuditResult
    (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayLocallySoluble
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (classification :
        ∀ row column,
          routingCell routing.routing row column ≠ 1 →
          ∀ w : AwayRoutingPrimeWitness routing,
            w.row = row → w.column = column → w.q ≠ 7 →
            Nonempty
              (AwayNonSevenLocalSolubilitySource w.q row column))
```

A less cumbersome but equally strong packet is acceptable. Do not fabricate a
closure provider.

Prove the checkpoint summit from every `CounterexamplePack`:

```lean
theorem firstResidueLocalAuditResult_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (FirstResidueLocalAuditResult x y z)
```

The report must say plainly, if proved:

```text
The nine first-residue local systems are not an obstruction by themselves.
Every actual non-seven local witness belongs to an explicitly soluble family.
```

This is a positive classification theorem, not a negative statement about all
possible stronger local or global obstructions.

# Optional prime-residue refinement

Only after Parts A-H are complete, investigate the primes admitting a root of
`leftCubicNormalized` / `rightCubicNormalized`.

The expected classification for primes `q != 7` is:

```text
root exists only when q ≡ 1 or -1 mod 7.
```

The two cubics have equivalent root existence via `t -> -t-1`.

This refinement may require a quadratic extension or cyclotomic finite-field
API. It is optional for Outcome A. Do not block the main local-solubility audit
on this classification.

# Tests

Focused tests must cover:

- all four normalization/homogenization identities;
- both explicit Bezout/resultant identities;
- correction nonvanishing at cubic roots for `q != 7`;
- the three `sevenV` row constructors;
- the three left-cubic row constructors;
- the three right-cubic row constructors;
- conversion of an abstract non-seven routing witness to a local solution;
- extraction of normalized cubic roots from actual `P,Q` witnesses;
- final honest audit route.

Use symbolic primes and abstract roots where possible. Avoid finite exhaustive
search and `native_decide`.

# Required report

Record:

- exact theorem/definition/structure surface;
- normalized polynomial and homogenization identities;
- the two Bezout/resultant certificates;
- correction nonvanishing for `q != 7`;
- explicit parametric solutions for all nine systems;
- conversion from actual routing witnesses;
- whether the optional prime-residue classification was completed;
- the final local-solubility audit route;
- recommended FLT7-015 boundary.

The recommended FLT7-015 boundary should move beyond first-residue
solubility. Audit one or more of:

```text
q^2 or higher congruence constraints;
exact q-adic valuation of a routing cell and its first-coordinate remainder;
full-cell signed factor compatibility rather than a single prime witness;
global reconstruction from all nine cells simultaneously.
```

The completed routing, pivot, and first-coordinate work must be reused rather
than repeated.

# Non-goals

Do not add:

- an unconditional `AwayDescentClosureProvider`;
- recursive descent;
- an FLT7 contradiction/no-solution theorem;
- a claim that local solubility implies a global integer solution;
- exhaustive enumeration over arbitrary `q`;
- general odd-prime cyclotomic theory;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: all nine local systems are classified and explicitly soluble in
  the stated conditional sense; actual non-seven witnesses are routed into
  these families; the first-residue obstruction is formally shown
  insufficient by itself.
- Outcome B: resultant certificates and most local constructors are complete,
  but one or more witness-conversion or audit packets require a precise
  follow-up.
- Outcome C: one of the expected parametric constructions fails or a local
  system is genuinely impossible; report the exact row/column and exploit the
  obstruction without claiming more than proved.

Commit with a focused message and push to the current feature branch.
