# FLT7TC-005R2 — Prescribed-carrier additive Fermat chart normalization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Treat `report-006.md` / FLT7TC-005R as fixed checked input.

The previous checkpoint proved that the two historical reconstruction failures
normalize to the common predicate

```lean
def AwayCarrierReconstruction (carrier : ℕ) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = carrier
```

and that this predicate still requires an actual away FLT7 counterexample.

This checkpoint must remove the remaining route/root packaging from the
statement of the reconstruction problem.  The goal is to identify
`AwayCarrierReconstruction carrier` with a purely additive primitive Fermat
chart in which the prescribed natural number is exactly the selected away
exceptional carrier.

Do **not** attempt FLT7TC-006 primitive closure in this checkpoint.
Do **not** construct a counterexample by assumption.
Do **not** use a theorem whose conclusion is already FLT7 contradiction.

## 1. Read first

Read the exact current versions of:

```text
DkMath/FLT/Seven/Basic.lean
DkMath/FLT/Seven/CoordinateNormalForm.lean
DkMath/FLT/Seven/ModSevenSectors.lean
DkMath/FLT/Seven/AwayValuationTransfer.lean
DkMath/FLT/Seven/DescentClosureAudit.lean
DkMath/FLT/Seven/PrimeTraceOneReconstructionKernel.lean
DkMath/FLT/Seven/PrimeTraceOneReconstructionKernelU16.lean
DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean
```

Also inspect the existing implementation of `CounterexamplePack.swapXY` if it
is useful, but do not assume that swapping identifies the three prescribed
carrier charts.

Relevant checked facts include:

```text
coordinateCounterexampleRoute_of_pack
awayExceptionalFactor_of_packet
nonempty_awayValuationTransferPacket
sevenEndpointResidueSector_of_counterexample
AwayExceptionalCarrierSource
AwayCarrierReconstruction
awayCarrierReconstruction_iff_nonempty_descentClosureProvider
internalDepthFourReconstruction_iff_awayCarrierReconstruction
```

## 2. Preferred module boundary

Prefer a new light production module such as

```text
DkMath/FLT/Seven/PrimeTraceOneReconstructionChart.lean
```

It may import the common reconstruction kernel and the shallow coordinate /
mod-seven routing surface.

If a U1.6 corollary would force the heavy fusion import into the light module,
put it in a separate leaf such as

```text
DkMath/FLT/Seven/PrimeTraceOneReconstructionChartU16.lean
```

The ordinary light chart module must not import the degree-six/U1.6 tower
merely for convenience.

## 3. Define the additive prescribed-carrier chart

Introduce the smallest honest proposition that says the prescribed natural
number is one of the three away exceptional factors of an actual primitive
FLT7 counterexample.

A preferred shape is an inductive proposition conceptually equivalent to:

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

Names may differ if there is a clearly better existing convention, but retain
which of `y`, `z`, or `y+z` is the prescribed carrier.

Do not include TraceOne roots, seventh-power roots, routing grids, valuation
packets, or reconstruction providers in this proposition.

## 4. Main equivalence

Prove the central normalization theorem:

```lean
AwayCarrierReconstruction carrier ↔ AwayCarrierFermatChart carrier
```

Suggested public name:

```text
awayCarrierReconstruction_iff_fermatChart
```

or an equally explicit name.

### 4.1 Forward direction

From

```text
∃ x y z route, route.carrier = carrier
```

use `route.source : AwayExceptionalCarrierSource ...`.

The source already records exactly one of:

```text
carrier = y
carrier = z
carrier = y + z
```

with the corresponding `7 ∣ ...` fact.  Recover the actual
`CounterexamplePack` from

```text
route.normal.counterexample
```

and construct the additive chart.

No new mathematics should be needed in this direction.

### 4.2 Reverse direction

This direction is the important audit.

Starting only from an additive chart, reconstruct an
`AwayValuationTransferPacket` using the existing checked route machinery.

For each of the three cases:

1. start from the stored `CounterexamplePack`;
2. use the existing coordinate/quadratic counterexample route;
3. prove that the ramified branch is impossible from the prescribed
   `7 ∣ carrier` condition;
4. obtain an `AwayCoordinateNormalForm`;
5. use `nonempty_awayValuationTransferPacket`;
6. inspect its `AwayExceptionalCarrierSource` and eliminate the two source
   constructors incompatible with `7 ∣ carrier`;
7. recover exact `route.carrier = carrier`.

For the three ramified exclusions, use checked divisibility/residue facts, not
informal modular reasoning.

Conceptually:

- right chart (`carrier = y`): ramified has `7 ∤ y`;
- left chart (`carrier = z`): ramified has `7 ∣ z-y` and `7 ∤ y`, so `7 ∣ z`
  would force `7 ∣ y`;
- sum chart (`carrier = y+z`): ramified has `z ≡ y (mod 7)` and `7 ∤ y`, so
  `7 ∣ y+z` would force `7 ∣ 2*y`, hence `7 ∣ y`, impossible.

It is acceptable to prove these through `ZMod 7` / `SevenEndpointResidueSector`
if that is shorter and clearer.

Do not assume the result of `awayExceptionalFactor_of_packet` before the away
packet has actually been obtained.

## 5. Expose the exact additive decomposition

Provide small API lemmas showing that a reconstructible carrier is exactly an
actual primitive FLT7 carrier of one of the three forms.

Useful consequences include proposition-level forms such as:

```text
AwayCarrierReconstruction carrier ->
  (∃ x z, CounterexamplePack x carrier z) ∨
  (∃ x y, CounterexamplePack x y carrier) ∨
  (∃ x y z, CounterexamplePack x y z ∧ y + z = carrier)
```

and retain the already proved necessary fact

```text
7 ∣ carrier.
```

Do not weaken `CounterexamplePack` to a bare numerical Fermat equality.
Positivity and primitiveness are part of the reconstruction contract.

## 6. Fixed-carrier size bounds

The chart normalization should expose a useful asymmetry between the three
additive charts.

### 6.1 Left / RHS chart

For a chart

```text
pack : CounterexamplePack x y carrier
```

prove the strict bounds

```text
x < carrier
y < carrier
```

using positivity and the Fermat equation.

### 6.2 Sum chart

For

```text
pack : CounterexamplePack x y z
hcarrier : y + z = carrier
```

prove

```text
x < carrier
y < carrier
z < carrier
```

The existing `right_lt_of_fermat7Equation` should give `x < z` or `y < z`
after the appropriate elementary argument; do not invoke an FLT theorem.

### 6.3 Right / second-summand chart

For

```text
pack : CounterexamplePack x carrier z
```

record only bounds that actually follow, for example

```text
carrier < z
x < z
```

Do **not** claim `z < carrier` or any finite bound in terms of `carrier` unless
it is independently proved.

The report must explicitly note this asymmetry:

- `carrier = z` and `carrier = y+z` are bounded finite-coordinate charts for a
  fixed carrier;
- `carrier = y` does not receive the same immediate bound from the current
  API.

No brute-force search is required in this checkpoint.

## 7. Symmetry audit

Check whether existing exact symmetries (`CounterexamplePack.swapXY` and any
other already checked maps) genuinely identify any of the three
`AwayCarrierFermatChart` constructors while preserving the **same prescribed
carrier**.

Do not conflate:

```text
same Fermat equation up to swapping x/y
```

with

```text
same prescribed away carrier.
```

If no checked carrier-preserving equivalence exists, report the three charts as
separate additive cases.

Do not import terminal-depth Row-Y/Row-Z/Row-Sum results to eliminate a general
chart: those theorems have additional terminal provenance and cannot be
silently generalized.

## 8. Transport existing terminal and U1.6 boundaries

Once the main equivalence is proved, expose shallow corollaries without
re-proving their arithmetic.

### 8.1 Depth-one away predecessor

For

```text
p : AwayValuationTransferPacket x y z
padicValNat 7 p.carrier = 1
```

transport the existing
`no_reconstruction_at_depth_one` theorem to obtain conceptually:

```text
¬ AwayCarrierFermatChart (Int.natAbs p.normal.root.snd)
```

This is still a terminal classification, not FLT contradiction.

### 8.2 U1.6

In the heavy leaf, if dependency direction is clean, prove the direct
normalization

```text
InternalDepthFourCounterexampleReconstructionObligation p ↔
  AwayCarrierFermatChart (internalDepthFourCarrier p)
```

by composing already checked equivalences.

Do not duplicate U1.6 arithmetic.

## 9. What this checkpoint must answer

`report-007.md` must answer explicitly:

1. Is `AwayCarrierReconstruction carrier` exactly equivalent to the proposed
   additive prescribed-carrier Fermat chart?
2. Does the reverse implication require any genuinely new algebraic theorem,
   or only existing counterexample routing and one-hot mod-seven facts?
3. Are the three carrier positions reducible to fewer cases while preserving
   the same prescribed carrier?
4. Which charts have all coordinates bounded by the fixed carrier?
5. Does this normalization construct any previously missing counterexample?
6. Is U1.6 now seen purely as the existence of an additive FLT7 chart with a
   prescribed depth-four carrier?

## 10. Audits

Add focused API and axiom audits, for example:

```text
DkMathTest/FLT/SevenPrimeTraceOneReconstructionChartApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOneReconstructionChartAxiomAudit.lean
```

Pin at least:

- the main reconstruction/chart equivalence;
- forward additive decomposition;
- the left-chart bounds;
- the sum-chart bounds;
- the right-chart honest bounds;
- the depth-one chart impossibility;
- the U1.6 chart equivalence if implemented.

Use `#print axioms` on the public main theorems.

Expected inherited axiom surface is only the standard project foundation
already observed (`propext`, `Classical.choice`, `Quot.sound`).

No new project axiom, `sorryAx`, `sorry`, `admit`, or `unsafe` proof.

## 11. Validation

At minimum run focused builds for:

```text
DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel
DkMath.FLT.Seven.CoordinateNormalForm
DkMath.FLT.Seven.ModSevenSectors
DkMath.FLT.Seven.AwayValuationTransfer
DkMath.FLT.Seven.PrimeTraceOneReconstructionChart
DkMath.FLT.Seven
```

plus any heavy U1.6 chart leaf and both focused audits if added.

Also run:

```text
forbidden-source scan
git diff --check
```

## 12. Documentation / roadmap

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-007.md
```

On success, update the campaign roadmap with a new intermediate checkpoint:

```text
FLT7TC-005R2 — Prescribed-carrier additive Fermat chart normalization
```

Do not mark FLT7TC-006 complete unless an actual primitive branch contradiction
has independently been constructed.

If this checkpoint only normalizes the reconstruction statement, leave
FLT7TC-006 blocked.

## 13. Outcome classification

Use exactly one of:

```text
Outcome A — PRESCRIBED-CARRIER ADDITIVE CHART CLOSES THE RECONSTRUCTION FRONTIER
```

Only if the checked additive chart analysis actually constructs the missing
provider/counterexample or proves the relevant reconstruction impossible in
all admissible cases.

```text
Outcome B — RECONSTRUCTION = PRESCRIBED-CARRIER ADDITIVE FLT7 CHART; NO NEW COUNTEREXAMPLE
```

Use this if the exact equivalence and size/symmetry audit are green but no
actual chart/provider is constructed or excluded generally.

```text
Outcome C — FORWARD ADDITIVE NORMALIZATION GREEN; REVERSE CHART-TO-AWAY ROUTE NEEDS A NEW BRIDGE
```

Use this only if a precise checked obstruction prevents reconstructing the
existing away route from an additive chart.

## 14. Hard boundaries

Do not:

- treat the existence of a seventh-power root as a new Fermat triple;
- treat `7 ∣ carrier` as sufficient for reconstruction;
- identify an arbitrary natural solution of a modular equation with a
  `CounterexamplePack`;
- infer a general chart contradiction from terminal-depth Row-Y/Row-Z/Row-Sum
  results;
- assume the three chart constructors are symmetry-equivalent;
- perform an unbounded numerical search and call it a proof;
- assume recursive descent or a well-founded transition;
- mark FLT7TC-006 or FLT7 unconditionality complete without a checked branch
  contradiction;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.
