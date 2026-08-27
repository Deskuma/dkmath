# FLT7-011 — Away second-coordinate valuation transfer

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-010.

## Objective

Convert the away second-coordinate identity into an exact `7`-adic transfer
packet.

For an away coordinate normal form with root

```text
root = (u,v),
```

prove

```text
y*z*(y+z) = 7 * |v| * |SndCore(u,v)|,
7 ∤ SndCore(u,v).
```

The one-hot exceptional endpoint factor

```text
E ∈ {y,z,y+z}
```

is the only factor on the left carrying `7`. Therefore prove the exact depth
transfer

```text
padicValNat 7 E
  = 1 + padicValNat 7 (Int.natAbs v).
```

Consequently expose

```text
padicValNat 7 (Int.natAbs v) < padicValNat 7 E,
49 ∣ E  <->  (7 : ℤ) ∣ v.
```

This checkpoint creates a strict `7`-adic measure drop, but it must not be
called a descent: `Int.natAbs v` is not yet proved to be an endpoint of a new
counterexample packet.

## New modules

Create:

```text
DkMath/FLT/Seven/AwaySecondCoordinateLoad.lean
DkMath/FLT/Seven/AwayValuationTransfer.lean
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenAwaySecondCoordinateLoad.lean
DkMathTest/FLT/SevenAwayValuationTransfer.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-011.md
```

Suggested imports:

```lean
-- AwaySecondCoordinateLoad.lean
import DkMath.FLT.Seven.ModSevenSectors

-- AwayValuationTransfer.lean
import DkMath.FLT.Seven.AwaySecondCoordinateLoad
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

Open `DkMath.NumberTheory.TraceOneQuadratic` locally where needed.

# Part A — Away root norm is outside the ramified channel

Prove that an away seventh-power root has norm not divisible by `7`.

Required theorem:

```lean
theorem AwayCoordinateNormalForm.root_norm_not_seven_dvd
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    ¬ (7 : ℤ) ∣ norm p.root
```

Recommended proof architecture:

1. the coordinate equality gives

```text
norm(cyclotomicSevenToTraceOne z y) = norm(root)^7;
```

2. the natural GN/cyclotomic bridge identifies the left side with

```text
GN 7 (z-y) y;
```

3. primitive endpoint coprimality and `p.seven_not_dvd_gap` imply

```text
7 ∤ GN 7 (z-y) y
```

using either `seven_dvd_GN_seven_sub_iff` or
`padicValNat_GN_seven_sub_eq_if`;
4. if `7∣norm root`, primality makes `7` divide its seventh power, contradiction.

Also expose the inherited core nondivisibility:

```lean
theorem AwayCoordinateNormalForm.sndCore_not_seven_dvd
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    ¬ (7 : ℤ) ∣
      seventhPowerSndCore p.root.fst p.root.snd
```

This should be a direct application of
`seven_not_dvd_seventhPowerSndCore_of_norm`.

# Part B — Exact absolute-value second-coordinate identity

First expose the signed cyclotomic identity in the orientation used downstream:

```lean
theorem cyclotomicSevenSnd_eq_neg_endpoint_product
    (z y : ℤ) :
    cyclotomicSevenSnd z y = -(y * z * (y+z))
```

Then prove the natural absolute-value identity:

```lean
theorem away_endpoint_product_eq_natAbs_seventhPowerSnd
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y+z) =
      Int.natAbs
        (seventhPowerSnd p.root.fst p.root.snd)
```

Use `p.snd_eq`, the explicit cyclotomic second coordinate, positivity of the
natural factors, and `Int.natAbs_neg`/casts. Keep sign normalization localized.

Now combine with

```text
seventhPowerSnd = 7*v*SndCore
```

and `Int.natAbs_mul` to prove the exact load decomposition:

```lean
theorem away_endpoint_product_load_eq
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    y * z * (y+z) =
      7 * Int.natAbs p.root.snd *
        Int.natAbs
          (seventhPowerSndCore p.root.fst p.root.snd)
```

Prove the nonzero facts needed by `padicValNat.mul`:

```lean
theorem AwayCoordinateNormalForm.root_snd_ne_zero
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    p.root.snd ≠ 0
```

```lean
theorem AwayCoordinateNormalForm.sndCore_ne_zero
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    seventhPowerSndCore p.root.fst p.root.snd ≠ 0
```

The core result follows immediately from nondivisibility by `7`. For the root
second coordinate, use the positive endpoint product and the load identity.

Expose natural nondivisibility of the absolute core:

```lean
theorem AwayCoordinateNormalForm.seven_not_dvd_natAbs_sndCore
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    ¬ 7 ∣ Int.natAbs
      (seventhPowerSndCore p.root.fst p.root.snd)
```

# Part C — Generic one-hot valuation isolation

Prove a small reusable natural-number lemma specialized to prime `7`.

One acceptable surface is:

```lean
theorem padicValNat_unique_factor_of_triple
    {a b c : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hb : ¬ 7 ∣ b) (hc : ¬ 7 ∣ c) :
    padicValNat 7 (a*b*c) = padicValNat 7 a
```

Use `padicValNat.mul` and `padicValNat.eq_zero_of_not_dvd`.

Also prove the right-load formula:

```lean
theorem padicValNat_seven_mul_of_core_not_dvd
    {v core : ℕ}
    (hv0 : v ≠ 0) (hc0 : core ≠ 0)
    (hc : ¬ 7 ∣ core) :
    padicValNat 7 (7*v*core) =
      1 + padicValNat 7 v
```

An equivalent multiplication order is acceptable. Avoid a general-prime
abstraction in this checkpoint.

# Part D — Branchwise exact valuation transfer

For each `AwayExceptionalFactor` constructor, prove the exact transfer.

Y/right branch:

```lean
theorem away_right_padicValNat_transfer
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z)
    (hy : 7 ∣ y)
    (hz : ¬ 7 ∣ z)
    (hsum : ¬ 7 ∣ y+z) :
    padicValNat 7 y =
      1 + padicValNat 7 (Int.natAbs p.root.snd)
```

Z/left branch:

```lean
theorem away_left_padicValNat_transfer
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z)
    (hz : 7 ∣ z)
    (hy : ¬ 7 ∣ y)
    (hsum : ¬ 7 ∣ y+z) :
    padicValNat 7 z =
      1 + padicValNat 7 (Int.natAbs p.root.snd)
```

Sum branch:

```lean
theorem away_sum_padicValNat_transfer
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z)
    (hsum : 7 ∣ y+z)
    (hy : ¬ 7 ∣ y)
    (hz : ¬ 7 ∣ z) :
    padicValNat 7 (y+z) =
      1 + padicValNat 7 (Int.natAbs p.root.snd)
```

Use the exact endpoint-product load identity on the right and unique-factor
isolation on the left. Do not prove the three cases by unrelated residue
arguments.

# Part E — Unified exceptional carrier packet

Define provenance for the selected natural carrier:

```lean
inductive AwayExceptionalCarrierSource
    (y z carrier : ℕ) : Prop
  | right
      (hy : 7 ∣ y)
      (hz : ¬ 7 ∣ z)
      (hsum : ¬ 7 ∣ y+z)
      (hcarrier : carrier = y)
  | left
      (hz : 7 ∣ z)
      (hy : ¬ 7 ∣ y)
      (hsum : ¬ 7 ∣ y+z)
      (hcarrier : carrier = z)
  | sum
      (hsum : 7 ∣ y+z)
      (hy : ¬ 7 ∣ y)
      (hz : ¬ 7 ∣ z)
      (hcarrier : carrier = y+z)
```

The equality field may be replaced by constructor-indexed definitional
carrier values if Lean elaborates that form cleanly.

Define:

```lean
structure AwayValuationTransferPacket
    (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  carrier : ℕ
  source : AwayExceptionalCarrierSource y z carrier
  carrier_pos : 0 < carrier
  root_snd_abs_pos : 0 < Int.natAbs normal.root.snd
  valuation_eq :
    padicValNat 7 carrier =
      1 + padicValNat 7 (Int.natAbs normal.root.snd)
```

Prove construction:

```lean
theorem nonempty_awayValuationTransferPacket
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayValuationTransferPacket x y z)
```

Use `awayExceptionalFactor_of_packet` and the three branchwise transfer
theorems.

Expose a chosen packet:

```lean
noncomputable def awayValuationTransferPacket
    {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    AwayValuationTransferPacket x y z :=
  Classical.choice (nonempty_awayValuationTransferPacket p)
```

# Part F — Exact carry and strict depth consequences

Prove the exact divisibility carry:

```lean
theorem AwayValuationTransferPacket.fortyNine_dvd_carrier_iff
    {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    49 ∣ p.carrier ↔ (7 : ℤ) ∣ p.normal.root.snd
```

Recommended proof route:

1. use `p.valuation_eq`;
2. translate `49∣carrier` to `2≤padicValNat 7 carrier`;
3. rewrite to `1≤padicValNat 7 (natAbs root.snd)`;
4. translate back to `7∣natAbs root.snd`;
5. bridge natural absolute-value divisibility to integer divisibility.

A direct proof through `fortyNine_dvd_seventhPowerSnd_iff` and the one-hot
source is also acceptable, but the valuation proof is preferred because it
certifies the same measure used below.

Prove the strict depth drop:

```lean
theorem AwayValuationTransferPacket.root_snd_depth_lt_carrier
    {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    padicValNat 7 (Int.natAbs p.normal.root.snd) <
      padicValNat 7 p.carrier
```

This should close immediately from `p.valuation_eq`.

Also expose the carrier's positive depth:

```lean
theorem AwayValuationTransferPacket.one_le_carrier_depth
    {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    1 ≤ padicValNat 7 p.carrier
```

# Part G — Full valuation route

Retain the ramified branch unchanged and replace the away branch by its exact
valuation packet.

```lean
inductive ValuationCounterexampleRoute (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | away (packet : AwayValuationTransferPacket x y z)
```

Prove the checkpoint summit:

```lean
theorem valuationCounterexampleRoute_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (ValuationCounterexampleRoute x y z)
```

Route through `coordinateCounterexampleRoute_of_pack`; in the away case build
the transfer packet.

# Tests

Focused tests must cover abstract wiring only:

- away root norm nondivisibility;
- exact endpoint-product absolute-value identity;
- exact `7*|v|*|SndCore|` decomposition;
- nonzero root second coordinate and core;
- all three branchwise valuation equations;
- construction of each carrier provenance constructor;
- `49∣carrier ↔ 7∣root.snd`;
- strict `padicValNat` depth decrease;
- both constructors of `ValuationCounterexampleRoute`.

Do not instantiate an actual counterexample.
Avoid `native_decide`.

# Required report

Record:

- exact theorem/definition/structure surface;
- proof that the away root norm is outside the `7` channel;
- signed-to-natural second-coordinate normalization;
- exact endpoint-product load decomposition;
- why the core contributes valuation zero;
- each one-hot valuation-transfer equation;
- unified carrier packet and provenance;
- exact `49` carry equivalence;
- strict `7`-adic depth drop;
- final valuation route;
- recommended FLT7-012 boundary.

The report must explicitly distinguish:

```text
proved strict depth drop
```

from

```text
not yet proved recursive descent.
```

The recommended FLT7-012 boundary should investigate closure: determine
whether the root coordinates and the selected exceptional carrier canonically
produce a new primitive FLT7/cyclotomic packet. Only if such a target packet is
constructed should the strict depth theorem be promoted to a descent step.
Otherwise expose the precise missing reconstruction provider.

# Non-goals

Do not add:

- a recursive counterexample transformation;
- a descent theorem;
- an FLT7 contradiction or no-solution theorem;
- a claim comparing ordinary numerical sizes of the carrier and root second
  coordinate;
- general LTE;
- a general-prime valuation-transfer abstraction;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: exact load decomposition, three branchwise valuation transfers,
  unified carrier packet, strict depth drop, and full valuation route are
  complete.
- Outcome B: exact load decomposition and branchwise transfers are complete,
  but the unified packet or full route needs a clearly identified follow-up.
- Outcome C: the proposed valuation equality is false; report the explicit
  arithmetic obstruction and preserve FLT7-010.

Commit with a focused message and push to the current feature branch.
