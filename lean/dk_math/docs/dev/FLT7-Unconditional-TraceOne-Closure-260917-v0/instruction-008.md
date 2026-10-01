# FLT7TC-005R3 — Prescribed-carrier chart to common ramified summit resolution

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the completed FLT7TC-005R2 result:

```text
AwayCarrierReconstruction carrier
  ↔ AwayCarrierFermatChart carrier
```

and does **not** assume that any such chart exists.  Its purpose is to resolve
what an inhabited prescribed-carrier chart would imply.

The key historical observation to audit is that the old terminal chart
resolution appears to use much less terminal provenance than its public types
suggest:

- the old Row-Y proof uses only a primitive `CounterexamplePack` and
  `7 ∣ y` to show that `swapXY` lies in the natural ramified branch;
- the old Row-Sum contradiction appears to use only a primitive
  `CounterexamplePack` and `7 ∣ y+z`;
- the old Row-Z alternating split / signed residual extraction appears to use
  only a primitive `CounterexamplePack`, `7 ∣ z`, and the consequences
  `7 ∣ x+y`, `7 ∤ y`.

The checkpoint must determine whether those statements can honestly be
**de-terminalized** and then package both surviving chart positions into the
existing common `PrimitiveRamifiedSummitPacket`.

Do not use terminal row/profile provenance unless the proof genuinely needs it.
Do not claim that the prescribed-carrier chart itself exists.

---

## 1. Fixed checked input

Use the current branch state, especially:

```text
DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel
DkMath.FLT.Seven.PrimeTraceOneReconstructionChart
DkMath.FLT.Seven.PrimeTraceOneReconstructionChartU16
DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge
DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution
DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore
DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
```

The established additive chart is:

```lean
inductive AwayCarrierFermatChart (carrier : ℕ) : Prop
  | right {x z : ℕ}
      (pack : CounterexamplePack x carrier z)
      (seven_dvd_carrier : 7 ∣ carrier)
  | left {x y : ℕ}
      (pack : CounterexamplePack x y carrier)
      (seven_dvd_carrier : 7 ∣ carrier)
  | sum {x y z : ℕ}
      (pack : CounterexamplePack x y z)
      (carrier_eq : y + z = carrier)
      (seven_dvd_carrier : 7 ∣ carrier)
```

The common integer ramified endpoint is:

```lean
PrimitiveRamifiedSummitPacket
```

whose `distinguished : ℤ` field must retain the prescribed natural carrier when
this checkpoint constructs a summit.

---

## 2. First target: de-terminalize the sum-chart contradiction

Audit

```lean
AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
```

carefully.

The terminal profile is currently used to obtain `7 ∣ y+z`.  The remainder of
the proof appears to depend only on:

```text
source : CounterexamplePack x y z
7 ∣ y + z
```

Promote the honest general theorem, conceptually:

```lean
theorem no_counterexample_of_seven_dvd_y_add_z
    {x y z : ℕ}
    (source : CounterexamplePack x y z)
    (hsum : 7 ∣ y + z) : False
```

Naming may follow repository conventions, but the theorem must be public and
must not mention terminal packets.

Preferred proof route:

1. use `sevenEndpointResidueSector_of_counterexample source`;
2. show the ramified / awayRight / awayLeft sectors contradict `7 ∣ y+z`;
3. in the awaySum sector, use `source.swapXY` and
   `coordinateCounterexampleRoute_of_pack`;
4. reject the swapped ramified branch because `7 ∤ z-x` in the awaySum residue
   sector;
5. reject the swapped away branch with
   `seven_dvd_endpoint_product_of_away`, because `x`, `z`, and `x+z` are all
   seven-units in that sector.

Do not import a terminal contradiction theorem as a black box if its proof can
be lowered to these assumptions.  The point of this checkpoint is precisely to
remove false provenance requirements.

Then expose:

```lean
AwayCarrierFermatChart.sum_impossible
```

or an equivalent theorem showing that the `sum` constructor cannot occur.

This is a genuine local contradiction for that chart position only.  It is not
FLT7 closure.

---

## 3. Second target: de-terminalize the right-chart natural ramified transition

Audit

```lean
AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
```

The theorem appears to use only:

```text
source : CounterexamplePack x y z
7 ∣ y
```

Promote the general theorem, conceptually:

```lean
theorem nonempty_swapped_ramified_of_seven_dvd_second
    {x y z : ℕ}
    (source : CounterexamplePack x y z)
    (hy : 7 ∣ y) :
    Nonempty (RamifiedCoordinateNormalForm y x z)
```

The proof should:

1. use `fermat7Equation_modSeven_linear source.hEq` to get `x ≡ z (mod 7)`;
2. use positivity to convert this to `7 ∣ z-x`;
3. route `source.swapXY` through `coordinateCounterexampleRoute_of_pack`;
4. eliminate the away constructor with its `seven_not_dvd_gap`;
5. return the ramified packet.

For a prescribed right chart

```lean
pack : CounterexamplePack x carrier z
7 ∣ carrier
```

this gives a natural ramified packet with first summand / distinguished natural
coordinate equal to `carrier`.

Use the existing

```text
RamifiedCoordinateNormalForm.seventhPower
SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
```

rather than rebuilding the natural summit.

---

## 4. Third target: de-terminalize the left-chart signed ramified extraction

This is the main arithmetic audit.

Start from only:

```text
source : CounterexamplePack x y z
hz : 7 ∣ z
```

In the prescribed left chart, `z = carrier`.

### 4.1 Structural consequences

Prove without terminal packets:

```text
7 ∣ x + y
7 ∤ y
7 ∤ x
```

The first follows from the mod-seven Fermat equation and `7 ∣ z`.
The unit facts follow from primitivity.

Also record the signed chart:

```text
(z : ℤ)^7 + (-(y : ℤ))^7 = (x : ℤ)^7
```

and the ramified signed gap:

```text
(7 : ℤ) ∣ (x : ℤ) - (-(y : ℤ))
```

if useful, but do not make the signed facade itself the endpoint.

### 4.2 General alternating seventh-power split

The old

```text
AwaySevenBaseTerminalRowZAlternatingPowerSplit
```

has fields

```text
a, b > 0
Coprime a b
x + y = 7^6 * a^7
alternatingCyclotomicSeven x y = 7 * b^7
z = 7 * a * b
```

Audit its constructor.  The current proof appears to use terminal provenance
only to obtain:

```text
7 ∣ x+y
7 ∤ y
7 ∣ z
```

Generalize this split to a packet/theorem whose assumptions are only
`source : CounterexamplePack x y z` and `hz : 7 ∣ z`.

Preferred implementation:

- factor out a light generic structure/theorem and make old terminal APIs
  wrappers if that reduces duplication;
- otherwise add a new generic structure in the new checkpoint module while
  reusing all universal lemmas already proved in
  `SevenBaseTerminalRowZAlternatingPowerSplit`:

```text
alternatingCyclotomicSeven
add_mul_alternatingCyclotomicSeven
alternatingCyclotomicSeven_intCast
gcd_add_alternatingCyclotomicSeven_dvd_seven
gcd_add_alternatingCyclotomicSeven_eq_seven
```

Do not duplicate the cyclotomic polynomial expansion unless unavoidable.

### 4.3 General signed residual core and seventh root

Likewise de-terminalize the useful part of

```text
AwaySevenBaseTerminalRowZSignedResidualCore
```

for the same light assumptions.

The generic signed residual packet should retain at least:

```text
powerSplit
residualCore : TraceOneInt (-2)
cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) = sevenAxis * residualCore
residualCore ≠ 0
¬ sevenAxis ∣ residualCore
¬ (7 : ℤ) ∣ norm residualCore
norm residualCore = (b : ℤ)^7
```

Reuse:

```text
exists_cyclotomicSeven_terminal_core
rowZ_signed_cyclotomicSeven_coordinates_isCoprime
common_divisor_dvd_sevenAxis_of_coordinate_coprime
isUnit_of_dvd_sevenAxis_of_dvd_terminal
exists_eq_seventh_power_of_coprime_mul_eq_pow
```

The desired checked conclusion is an exact root:

```text
∃ root : TraceOneInt (-2),
  cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
    sevenAxis * root ^ 7
```

with the same natural split witnesses feeding the norm.

No norm-only inference of element equality is allowed.

---

## 5. Common prescribed-carrier summit wrapper

Introduce the smallest wrapper that retains the carrier identity, conceptually:

```lean
structure PrescribedCarrierRamifiedSummit (carrier : ℕ) : Type where
  summit : PrimitiveRamifiedSummitPacket
  distinguished_eq : summit.distinguished = (carrier : ℤ)
```

A different name is acceptable if clearer.

Construct it from both surviving chart positions.

### Right chart

For

```text
CounterexamplePack x carrier z
7 ∣ carrier
```

use the swapped natural ramified packet and the existing direct specialized
summit bridge.

### Left chart

For

```text
CounterexamplePack x y carrier
7 ∣ carrier
```

use the generalized alternating split + signed residual seventh root to build
`PrimitiveRamifiedSummitPacket` directly, with:

```text
endpointLeft  = x
endpointRight = -y
distinguished = carrier
gapRoot       = a
residualRoot  = b
```

and the exact equations:

```text
x - (-y) = 7^6 * a^7
cyclotomicSeven x (-y) = 7 * b^7
carrier = 7 * a * b
cyclotomicSevenToTraceOne x (-y) = sevenAxis * root^7
norm root = b
```

Prefer extracting/promoting a reusable root-norm helper from the historical
summit module over copy-pasting a long proof, provided this causes no import
cycle and preserves existing APIs.

### Sum chart

Eliminate it using the de-terminalized contradiction from §2.

---

## 6. Main resolution theorem

Target the proposition/type-level result:

```lean
theorem nonempty_prescribedCarrierRamifiedSummit_of_fermatChart
    {carrier : ℕ}
    (h : AwayCarrierFermatChart carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier)
```

Then compose with FLT7TC-005R/005R2:

```lean
AwayCarrierReconstruction carrier
  -> Nonempty (PrescribedCarrierRamifiedSummit carrier)
```

This theorem is **conditional on reconstruction**.  It does not construct a
new chart from divisibility alone.

Also expose the U1.6 corollary:

```text
InternalDepthFourCounterexampleReconstructionObligation p
  -> Nonempty
       (PrescribedCarrierRamifiedSummit (internalDepthFourCarrier p))
```

Do not claim that the U1.6 obligation is inhabited.

---

## 7. Required architectural audit

`report-008.md` must answer all of the following explicitly.

1. Can `7 ∣ y+z` be ruled out from `CounterexamplePack` alone?
2. Can `7 ∣ y` always be converted, after `swapXY`, to the natural ramified
   quadratic route without terminal provenance?
3. Can `7 ∣ z` always be converted to the signed alternating seventh-power
   split without terminal provenance?
4. Can the signed residual core then be extracted as an exact seventh power
   without terminal provenance?
5. Do right and left prescribed-carrier charts both enter the **same**
   `PrimitiveRamifiedSummitPacket` type while preserving
   `summit.distinguished = carrier`?
6. If not, identify the exact first theorem/field that genuinely needs terminal
   provenance.  Do not merely say “historical code is terminal-specific.”
7. Does this checkpoint construct an `AwayCarrierFermatChart` or
   `AwayCarrierReconstruction` witness?  Expected answer is **NO** unless an
   actual new proof is found.
8. What is the new precise frontier for FLT7TC-006 after this resolution?

The report should distinguish:

```text
existence of a prescribed-carrier chart
```

from

```text
resolution of an already-existing chart into ramified arithmetic.
```

They are not the same theorem.

---

## 8. Suggested file placement

Prefer a new production module such as:

```text
DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolution.lean
```

and, if the U1.6 import would make the light module heavy, a sibling:

```text
DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolutionU16.lean
```

A small reusable generic signed/alternating packet may live in the main
resolution module.

Do not make `DkMath.FLT.Prime` import specialized Seven code.

Update `DkMath/FLT/Seven.lean` only after the focused modules build.

---

## 9. API tests

Add focused API regression proving at least:

```text
sum chart contradiction
general right -> swapped ramified transition
general left -> signed exact seventh-power coordinate extraction
right -> prescribed-carrier common summit
left -> prescribed-carrier common summit
AwayCarrierReconstruction -> prescribed-carrier common summit
```

For witness-sensitive results, check the summit field:

```text
summit.distinguished = (carrier : ℤ)
```

Do not assert definitional equality for roots or `a,b` witnesses chosen by
independent existential proofs.

Add a separate `#print axioms` audit for the public declarations.

---

## 10. Validation

At minimum run:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionChart
lake build DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution
lake build DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
lake build DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore
lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolution
lake build DkMath.FLT.Seven
```

plus all new focused API / axiom audits.

Run the usual forbidden-source scan for:

```text
sorry
sorryAx
admit
axiom
unsafe
```

on fresh production/test sources, and run:

```text
git diff --check
```

No project axiom, hidden hypothesis, or theorem whose conclusion is already
FLT7 is permitted.

---

## 11. Outcomes

Use exactly one of these classifications.

### Outcome A — PRESCRIBED-CARRIER CHARTS RESOLVE TO COMMON RAMIFIED SUMMIT

Requirements:

- sum chart is impossible from `CounterexamplePack + 7 ∣ y+z` alone;
- right chart reaches natural ramified packet without terminal provenance;
- left chart reaches signed exact seventh-power quadratic packet without
  terminal provenance;
- both produce `PrescribedCarrierRamifiedSummit carrier`;
- `AwayCarrierReconstruction carrier` conditionally yields that common summit;
- builds/audits are green.

This does **not** mean reconstruction exists and does not close FLT7TC-006.

### Outcome B — SUM/RIGHT RESOLUTION GREEN; LEFT SIGNED EXTRACTION HAS A REAL NEW FRONTIER

Use this only if the terminal-independent Row-Z generalization fails for a
mathematically substantive reason.  `report-008.md` must identify the exact
missing theorem/data and explain why `CounterexamplePack + 7 ∣ z` is
insufficient.

### Outcome C — CHART RESOLUTION REQUIRES GENUINE TERMINAL PROVENANCE

Use this only if even the sum/right de-terminalizations fail because some
terminal invariant is genuinely used.  Identify the first irreducible field.

---

## 12. Hard stop rules

Do not:

- infer any prescribed-carrier chart from `7 ∣ carrier` alone;
- identify separately chosen seventh-power witnesses;
- infer an element equality from equality of norms;
- claim the sum contradiction eliminates right or left charts;
- claim a right-chart swap is a recursive descent step;
- claim the signed left chart is natural/positive after the odd permutation;
- silently use `TerminalPrimitiveRamifiedSummitPacket` or a terminal carrier;
- treat `PrimitiveRamifiedSummitPacket` as if it retained terminal provenance;
- claim FLT7TC-006 or FLT7TC-007 is complete;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project axiom.

The desired result of this checkpoint is a **resolution theorem for an assumed
reconstruction witness**, not the missing existence theorem itself.
