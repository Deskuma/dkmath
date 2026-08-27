# FLT7-010 — Explicit seventh-power coordinates and mod-seven endpoint sectors

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-009.

## Objective

Expand the two element-level normal forms from FLT7-009 into explicit integer
coordinate equations and extract their finite modulo-`7` residue sectors.

For a root

```text
gamma = u + v*tau,
```

prove explicit formulas for

```text
gamma^7
sevenAxis * gamma^7.
```

Then expose the characteristic-`7` collapse

```text
gamma^7 mod 7
  = (u+4v, 0),

sevenAxis*gamma^7 mod 7
  = (-(u+4v), 2(u+4v)).
```

Use the away formula to prove

```text
7 ∣ y*z*(z+y),
```

and primitive endpoint coprimality to show that exactly one of

```text
y,
z,
z+y
```

carries the factor `7`.

The final endpoint residue classification must consist of exactly four sectors:

```text
Ramified: (x,y,z) = (0,t,t)
Away-Y:   (x,y,z) = (t,0,t)
Away-Z:   (x,y,z) = (-t,t,0)
Away-Sum: (x,y,z) = (-2t,t,-t)
```

in `ZMod 7`, with `t ≠ 0`.

This checkpoint is a finite residue ledger. Do not claim a contradiction or a
decreasing transformation.

## New modules

Create:

```text
DkMath/FLT/Seven/SeventhPowerCoordinates.lean
DkMath/FLT/Seven/CoordinateNormalForm.lean
DkMath/FLT/Seven/ModSevenSectors.lean
```

Suggested imports:

```lean
-- SeventhPowerCoordinates.lean
import DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm

-- CoordinateNormalForm.lean
import DkMath.FLT.Seven.SeventhPowerCoordinates

-- ModSevenSectors.lean
import DkMath.FLT.Seven.CoordinateNormalForm
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenSeventhPowerCoordinates.lean
DkMathTest/FLT/SevenModSevenSectors.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-010.md
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Explicit seventh-power coordinate polynomials

Define the first coordinate polynomial:

```lean
def seventhPowerFst (u v : ℤ) : ℤ :=
  u ^ 7
    - 42 * u ^ 5 * v ^ 2
    - 70 * u ^ 4 * v ^ 3
    + 70 * u ^ 3 * v ^ 4
    + 126 * u ^ 2 * v ^ 5
    + 14 * u * v ^ 6
    - 10 * v ^ 7
```

Define the second coordinate polynomial:

```lean
def seventhPowerSnd (u v : ℤ) : ℤ :=
  7 * u ^ 6 * v
    + 21 * u ^ 5 * v ^ 2
    - 35 * u ^ 4 * v ^ 3
    - 105 * u ^ 3 * v ^ 4
    - 21 * u ^ 2 * v ^ 5
    + 35 * u * v ^ 6
    + 7 * v ^ 7
```

Prove:

```lean
theorem traceOne_pow_seven_fst (u v : ℤ) :
    ((⟨u,v⟩ : TraceOneInt (-2)) ^ 7).fst =
      seventhPowerFst u v
```

```lean
theorem traceOne_pow_seven_snd (u v : ℤ) :
    ((⟨u,v⟩ : TraceOneInt (-2)) ^ 7).snd =
      seventhPowerSnd u v
```

and the structured equality:

```lean
theorem traceOne_pow_seven_eq (u v : ℤ) :
    (⟨u,v⟩ : TraceOneInt (-2)) ^ 7 =
      ⟨seventhPowerFst u v, seventhPowerSnd u v⟩
```

A direct `norm_num`/`ring` proof through the explicit multiplication law is
acceptable. Do not introduce an external polynomial representation.

# Part B — Second-coordinate core and mod-seven collapse

Factor the universal `7*v` from the second coordinate.

```lean
def seventhPowerSndCore (u v : ℤ) : ℤ :=
  u ^ 6
    + 3 * u ^ 5 * v
    - 5 * u ^ 4 * v ^ 2
    - 15 * u ^ 3 * v ^ 3
    - 3 * u ^ 2 * v ^ 4
    + 5 * u * v ^ 5
    + v ^ 6
```

```lean
theorem seventhPowerSnd_eq_seven_mul
    (u v : ℤ) :
    seventhPowerSnd u v =
      7 * v * seventhPowerSndCore u v
```

Prove the key `ZMod 7` identity:

```lean
theorem seventhPowerSndCore_mod_seven
    (u v : ℤ) :
    (seventhPowerSndCore u v : ZMod 7) =
      ((u : ZMod 7) ^ 2 + (u : ZMod 7) * (v : ZMod 7)
        + 2 * (v : ZMod 7) ^ 2) ^ 3
```

This is the finite-field shadow

```text
SndCore ≡ norm(u,v)^3 mod 7.
```

Prove the coordinate collapse:

```lean
theorem seventhPowerFst_mod_seven
    (u v : ℤ) :
    (seventhPowerFst u v : ZMod 7) =
      (u : ZMod 7) + 4 * (v : ZMod 7)
```

```lean
theorem seventhPowerSnd_mod_seven
    (u v : ℤ) :
    (seventhPowerSnd u v : ZMod 7) = 0
```

Also prove the norm collapse:

```lean
theorem traceOneNorm_mod_seven_eq_linear_sq
    (u v : ℤ) :
    (norm (⟨u,v⟩ : TraceOneInt (-2)) : ZMod 7) =
      ((u : ZMod 7) + 4 * (v : ZMod 7)) ^ 2
```

Required consequence:

```lean
theorem seven_not_dvd_seventhPowerSndCore_of_norm
    {u v : ℤ}
    (hnorm : ¬ (7 : ℤ) ∣ norm (⟨u,v⟩ : TraceOneInt (-2))) :
    ¬ (7 : ℤ) ∣ seventhPowerSndCore u v
```

Strongly recommended exact carry theorem:

```lean
theorem fortyNine_dvd_seventhPowerSnd_iff
    {u v : ℤ}
    (hnorm : ¬ (7 : ℤ) ∣ norm (⟨u,v⟩ : TraceOneInt (-2))) :
    (49 : ℤ) ∣ seventhPowerSnd u v ↔
      (7 : ℤ) ∣ v
```

Use `seventhPowerSnd_eq_seven_mul`, nondivisibility of the core, and primality
of `7`. Do not use LTE.

# Part C — Axis-times-seventh-power coordinates

Define:

```lean
def ramifiedSeventhFst (u v : ℤ) : ℤ :=
  -u ^ 7
    - 28 * u ^ 6 * v
    - 42 * u ^ 5 * v ^ 2
    + 210 * u ^ 4 * v ^ 3
    + 350 * u ^ 3 * v ^ 4
    - 42 * u ^ 2 * v ^ 5
    - 154 * u * v ^ 6
    - 18 * v ^ 7
```

```lean
def ramifiedSeventhSnd (u v : ℤ) : ℤ :=
  2 * u ^ 7
    + 7 * u ^ 6 * v
    - 63 * u ^ 5 * v ^ 2
    - 175 * u ^ 4 * v ^ 3
    + 35 * u ^ 3 * v ^ 4
    + 231 * u ^ 2 * v ^ 5
    + 63 * u * v ^ 6
    - 13 * v ^ 7
```

Prove:

```lean
theorem sevenAxis_mul_pow_seven_eq (u v : ℤ) :
    sevenAxis * (⟨u,v⟩ : TraceOneInt (-2)) ^ 7 =
      ⟨ramifiedSeventhFst u v, ramifiedSeventhSnd u v⟩
```

Expose the simpler structural formulas:

```lean
theorem ramifiedSeventhFst_eq
    (u v : ℤ) :
    ramifiedSeventhFst u v =
      -seventhPowerFst u v - 4 * seventhPowerSnd u v
```

```lean
theorem ramifiedSeventhSnd_eq
    (u v : ℤ) :
    ramifiedSeventhSnd u v =
      2 * seventhPowerFst u v + seventhPowerSnd u v
```

Prove the mod-seven collapse:

```lean
theorem ramifiedSeventhFst_mod_seven
    (u v : ℤ) :
    (ramifiedSeventhFst u v : ZMod 7) =
      -((u : ZMod 7) + 4 * (v : ZMod 7))
```

```lean
theorem ramifiedSeventhSnd_mod_seven
    (u v : ℤ) :
    (ramifiedSeventhSnd u v : ZMod 7) =
      2 * ((u : ZMod 7) + 4 * (v : ZMod 7))
```

Thus the ramified coordinates lie on the line

```text
snd = -2*fst mod 7.
```

# Part D — Explicit coordinate normal-form packets

Define the away coordinate packet:

```lean
structure AwayCoordinateNormalForm (x y z : ℕ) : Type where
  counterexample : CounterexamplePack x y z
  seven_not_dvd_gap : ¬ 7 ∣ z-y
  root : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7
  fst_eq :
    cyclotomicSevenFst (z : ℤ) (y : ℤ) =
      seventhPowerFst root.fst root.snd
  snd_eq :
    cyclotomicSevenSnd (z : ℤ) (y : ℤ) =
      seventhPowerSnd root.fst root.snd
```

Define the ramified coordinate packet:

```lean
structure RamifiedCoordinateNormalForm (x y z : ℕ) : Type where
  seventhPower : SevenQuadraticSeventhPowerPacket x y z
  fst_eq :
    cyclotomicSevenFst (z : ℤ) (y : ℤ) =
      ramifiedSeventhFst seventhPower.root.fst seventhPower.root.snd
  snd_eq :
    cyclotomicSevenSnd (z : ℤ) (y : ℤ) =
      ramifiedSeventhSnd seventhPower.root.fst seventhPower.root.snd
```

Prove constructors from the FLT7-009 route data.

Define:

```lean
inductive CoordinateCounterexampleRoute (x y z : ℕ) : Type
  | away (packet : AwayCoordinateNormalForm x y z)
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
```

Prove:

```lean
theorem coordinateCounterexampleRoute_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (CoordinateCounterexampleRoute x y z)
```

# Part E — Away exceptional-factor trichotomy

From the away second-coordinate equation and

```text
cyclotomicSevenSnd z y = -z*y*(z+y),
```

prove:

```lean
theorem seven_dvd_endpoint_product_of_away
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    7 ∣ y * z * (y+z)
```

Then prove no two of the three factors can be divisible by `7` under primitive
endpoint coprimality.

Required pairwise exclusions:

```lean
¬ (7 ∣ y ∧ 7 ∣ z)
¬ (7 ∣ y ∧ 7 ∣ y+z)
¬ (7 ∣ z ∧ 7 ∣ y+z)
```

Package the exact one-hot trichotomy:

```lean
inductive AwayExceptionalFactor (y z : ℕ) : Prop
  | right
      (hy : 7 ∣ y)
      (hz : ¬ 7 ∣ z)
      (hsum : ¬ 7 ∣ y+z)
  | left
      (hz : 7 ∣ z)
      (hy : ¬ 7 ∣ y)
      (hsum : ¬ 7 ∣ y+z)
  | sum
      (hsum : 7 ∣ y+z)
      (hy : ¬ 7 ∣ y)
      (hz : ¬ 7 ∣ z)
```

```lean
theorem awayExceptionalFactor_of_packet
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    AwayExceptionalFactor y z
```

Constructor names may be improved, but avoid ambiguous orientation language in
the report.

# Part F — Four endpoint residue sectors

Use a small `ZMod 7` sector type. One recommended definition is:

```lean
abbrev ModSeven := ZMod 7

inductive SevenEndpointResidueSector (x y z : ℕ) : Prop
  | ramified (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = 0)
      (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = t)
  | awayRight (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = t)
      (hy : (y : ModSeven) = 0)
      (hz : (z : ModSeven) = t)
  | awayLeft (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = -t)
      (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = 0)
  | awaySum (t : ModSeven) (ht : t ≠ 0)
      (hx : (x : ModSeven) = -2*t)
      (hy : (y : ModSeven) = t)
      (hz : (z : ModSeven) = -t)
```

The names `awayRight/awayLeft` may be replaced by `awayY/awayZ` to match which
endpoint is divisible by `7`.

Prove the checkpoint summit:

```lean
theorem sevenEndpointResidueSector_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    SevenEndpointResidueSector x y z
```

Proof architecture:

1. split through `CoordinateCounterexampleRoute`;
2. ramified route:
   - `7∣z-y` gives `z=y` in `ZMod 7`;
   - primitive endpoint coprimality gives `y≠0`;
   - the Fermat equation and Frobenius `a^7=a` give `x=0`;
3. away route:
   - use `AwayExceptionalFactor`;
   - reduce the Fermat equation modulo `7` to `x+y=z`;
   - derive the corresponding projective line in each of the three cases;
   - prove the chosen scale `t` is nonzero from primitive coprimality.

Do not enumerate all `7^3` residue triples.

# Tests

The focused tests must cover:

- both explicit seventh-power coordinate identities;
- the `7*v*SndCore` factorization;
- `SndCore ≡ norm^3 mod 7`;
- the four mod-seven collapse formulas;
- construction of away and ramified coordinate packets from abstract route
  data;
- exact one-hot exceptional factor selection;
- all four endpoint residue-sector constructors through abstract hypotheses;
- the final sector theorem from an abstract `CounterexamplePack`.

Avoid `native_decide`.

# Required report

Record:

- exact polynomial definitions and theorem surface;
- the explicit coordinates of `gamma^7` and `sevenAxis*gamma^7`;
- the factorization of the second coordinate;
- the identity `SndCore ≡ norm^3 mod 7`;
- the Frobenius/double-root collapse at discriminant `-7`;
- both coordinate normal-form packets;
- the away exceptional-factor one-hot trichotomy;
- the four endpoint residue sectors;
- recommended FLT7-011 boundary.

The report should explicitly note the conceptual reason for the collapse:

```text
tau^2-tau+2 = (tau-4)^2 in characteristic 7,
```

so every seventh power loses its nilpotent coordinate modulo `7`.

The recommended FLT7-011 boundary should measure the exact extra `7`-adic load
in the away second-coordinate equation. In particular, combine

```text
seventhPowerSnd = 7*v*SndCore,
7∤SndCore,
```

with the unique exceptional endpoint factor to derive a valuation-transfer or
strict size transformation. Do not call it a descent until the target packet
and strict measure are explicit.

# Non-goals

Do not add:

- a contradiction or FLT7 no-solution theorem;
- a coordinate descent;
- a recursive transformation;
- general LTE;
- residue enumeration by `native_decide`;
- a general odd-prime coordinate theorem;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: explicit coordinates, mod-seven collapse, coordinate route,
  one-hot away factor, and four endpoint residue sectors are complete.
- Outcome B: explicit coordinates and route packets are complete, but the
  one-hot/sector classification requires a clearly identified follow-up.
- Outcome C: one of the explicit polynomial identities or sector claims is
  false; report the concrete counterexample and preserve FLT7-009.

Commit with a focused message and push to the current feature branch.
