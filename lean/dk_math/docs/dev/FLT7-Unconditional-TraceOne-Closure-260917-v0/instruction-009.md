# FLT7TC-005R4 — Primitive second-case classification and global ramified resolution

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

## Purpose

FLT7TC-005R3 changed the shape of the remaining problem more substantially than the old ROADMAP reflects.

We now have all of the following checked facts:

1. every primitive counterexample reaches `CoordinateCounterexampleRoute`;
2. every away coordinate packet has exactly one exceptional factor among `y`, `z`, `y+z`;
3. `no_counterexample_of_seven_dvd_y_add_z` eliminates the `y+z` case for an arbitrary `CounterexamplePack`, with no terminal provenance;
4. an actual chart with `7 ∣ y` reaches a natural ramified chart after summand exchange;
5. an actual chart with `7 ∣ z` reaches the generalized signed ramified extraction and then the common `PrimitiveRamifiedSummitPacket`;
6. an original ramified counterexample already reaches the same common summit through `SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket`.

Therefore do **not** continue treating the away branch as needing an independent contradiction before primitive branch closure.  The first task of this checkpoint is to prove, at the primitive natural counterexample level, that all surviving branches normalize into one ramified/second-case surface.

This is a normalization checkpoint, not an FLT7 contradiction checkpoint.

## Required reading

Read the current branch versions of:

- `DkMath/FLT/Seven/Basic.lean`
- `DkMath/FLT/Seven/CounterexampleRouting.lean`
- `DkMath/FLT/Seven/ModSevenSectors.lean`
- `DkMath/FLT/Seven/CoordinateNormalForm.lean`
- `DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean`
- `DkMath/FLT/Seven/PrimeTraceOneRamifiedSummitBridge.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionChart.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolution.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean`
- `docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-008.md`
- `docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/ROADMAP.md`

Historical terminal modules may be read for comparison, but the new primitive normalization theorem must not require terminal provenance.

## 1. Prove the primitive second-case classification

Introduce a small honest proposition/type recording that exactly one natural endpoint is divisible by seven.

A suggested shape is:

```lean
inductive PrimitiveSevenDivisibleEndpoint (x y z : ℕ) : Prop
  | xOnly (hx : 7 ∣ x) (hy : ¬ 7 ∣ y) (hz : ¬ 7 ∣ z)
  | yOnly (hy : 7 ∣ y) (hx : ¬ 7 ∣ x) (hz : ¬ 7 ∣ z)
  | zOnly (hz : 7 ∣ z) (hx : ¬ 7 ∣ x) (hy : ¬ 7 ∣ y)
```

Naming may be adjusted to repository style.

Target:

```lean
theorem primitiveSevenDivisibleEndpoint_of_counterexample
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    PrimitiveSevenDivisibleEndpoint x y z
```

Prefer the existing `sevenEndpointResidueSector_of_counterexample` as the classification source.

Expected branch behavior:

- `.ramified`: `x ≡ 0`, while `y,z` are the same nonzero residue;
- `.awayRight`: `y ≡ 0`, while `x,z` are nonzero;
- `.awayLeft`: `z ≡ 0`, while `x,y` are nonzero;
- `.awaySum`: derive `7 ∣ y+z` from the recorded residues and eliminate it with the already checked `no_counterexample_of_seven_dvd_y_add_z source`.

Do not prove uniqueness by inventing a fresh global number-theory argument if the existing residue-sector data already gives it directly.

Also expose convenient corollaries if useful:

```text
CounterexamplePack -> 7 ∣ x ∨ 7 ∣ y ∨ 7 ∣ z
CounterexamplePack -> not two endpoints are simultaneously divisible by 7
```

But avoid redundant API if the inductive result already provides a clean consumer surface.

### Interpretation

This is the checked `p=7` second-case reduction:

```text
primitive FLT7 counterexample
  -> exactly one of x,y,z is divisible by 7.
```

Do not call this an FLT contradiction.

## 2. Global primitive counterexample -> common ramified summit

Create a provenance-preserving resolution packet rather than returning only a bare existential summit.

A suggested shape is one of:

```lean
inductive PrimitiveCounterexampleRamifiedResolution
    {x y z : ℕ} (source : CounterexamplePack x y z) : Type
  | xCase ...
  | yCase ...
  | zCase ...
```

or a structure with an endpoint-source tag.

It must retain at least:

- the original `source : CounterexamplePack x y z` (directly or through the index);
- a `PrimitiveRamifiedSummitPacket`;
- which original endpoint (`x`, `y`, or `z`) became `summit.distinguished`;
- the exact equality of that distinguished coordinate with the original endpoint cast to `ℤ`;
- the corresponding checked `7`-divisibility fact.

Do not erase the orientation/provenance into only `Nonempty PrimitiveRamifiedSummitPacket`.

### x-divisible branch

For `7 ∣ x`, derive the original natural ramified gap `7 ∣ z-y` from the Fermat mod-seven relation (or an already checked equivalent lemma).  Then use the ordinary p=7 quadratic ramified constructor and existing direct summit bridge.

Conceptually:

```text
CounterexamplePack x y z
7 | x
  -> 7 | (z-y)
  -> SevenQuadraticSeventhPowerPacket x y z
  -> PrimitiveRamifiedSummitPacket
     distinguished = x
```

Do not route through the terminal tower.

### y-divisible branch

Reuse FLT7TC-005R3:

```text
CounterexamplePack x y z
7 | y
  -> swapXY
  -> natural RamifiedCoordinateNormalForm y x z
  -> common summit
     distinguished = y
```

Prefer the already public generalized theorem rather than duplicating its proof.

### z-divisible branch

Reuse the generalized signed extraction from FLT7TC-005R3:

```text
CounterexamplePack x y z
7 | z
  -> prescribed-carrier signed alternating split
  -> signed residual seventh power
  -> common summit
     distinguished = z
```

Again, do not reintroduce terminal Row-Z provenance.

### Main theorem

Target something conceptually equivalent to:

```lean
theorem nonempty_primitiveCounterexampleRamifiedResolution
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty (PrimitiveCounterexampleRamifiedResolution source)
```

A convenience corollary returning only `Nonempty PrimitiveRamifiedSummitPacket` is acceptable, but the provenance-preserving theorem is the primary endpoint.

## 3. Expose the generic summit distinguished-depth law

The common summit has

```text
distinguished = 7 * gapRoot * residualRoot
7 ∤ residualRoot
```

and all three factors are nonzero.  Therefore expose the exact generic valuation law, preferably in a light module near the common summit/depth API:

```lean
PrimitiveRamifiedSummitPacket.distinguished_padicValNat
```

with conceptual statement

```text
v7(|distinguished|) = 1 + v7(gapRoot).
```

Then combine it with the existing

```text
v7(|root.snd|) = 5 + 7*v7(gapRoot)
```

to obtain the useful eliminated form

```text
v7(|root.snd|) = 7 * v7(|distinguished|) - 2
```

or an equivalent subtraction-free formulation, for example

```text
v7(|root.snd|) + 2 = 7 * v7(|distinguished|).
```

Prefer the subtraction-free theorem if it produces a cleaner Nat statement.

This is an exact summit invariant, not a contradiction.

### Provenance pullback

For the new primitive resolution, expose the corresponding endpoint law in each source case, or one uniform theorem through the stored `distinguished_eq`:

```text
root second-coordinate depth + 2
  = 7 * depth(the unique 7-divisible original endpoint).
```

Do not silently identify different endpoints; use the resolution's source tag/equality.

## 4. U1.6 consequence audit

The existing U1.6 prescribed carrier has exact depth four.  FLT7TC-005R3 shows that, under the reconstruction obligation, it reaches a prescribed-carrier ramified summit.

Using the new distinguished-depth law, derive the exact consequences under that same existing assumption:

```text
v7(gapRoot) = 3
v7(|summit.root.snd|) = 26
```

because

```text
v7(distinguished) = 4 = 1 + v7(gapRoot)
rootSnd depth = 5 + 7*3 = 26.
```

Package this only as a conditional U1.6 corollary.  It is **not** a contradiction and it does not inhabit the reconstruction obligation.

This calculation is useful because it proves that a reconstructed U1.6 chart lands in a nonterminal ramified summit (`gapRoot` has depth three), so the historical terminal `gapRoot_not_seven_dvd` packet cannot be recovered merely from the new summit.

If clean, expose explicitly:

```text
7 ∣ summit.gapRoot
```

for the reconstructed U1.6 summit.

Do not infer that this makes the reconstruction impossible.

## 5. ROADMAP correction

If the global primitive-to-ramified resolution kernel-checks, update the campaign ROADMAP substantially.

The old FLT7TC-006 text says primitive closure waits for **separate contradictions in both away and ramified branches**.  That is no longer the correct architecture.

Record instead:

```text
primitive CounterexamplePack
  -> exactly one endpoint is divisible by 7
  -> provenance-preserving common ramified summit
```

Thus the away branch has been **absorbed into the ramified second-case surface**; it no longer needs an independent final contradiction.

FLT7TC-006 should remain blocked, but its honest remaining target becomes something like:

```text
counterexample-origin ramified summit -> False
```

or a stronger provenance-preserving ramified packet exclusion.

Do not state that arbitrary `PrimitiveRamifiedSummitPacket` is impossible unless that is actually proved.  Preserve counterexample provenance for the next checkpoint.

Also keep the historical reconstruction kernel material in the ROADMAP as a useful audited boundary, but make clear that it is no longer required to normalize the **original** away branch into the common ramified surface.

## 6. Implementation location

Suggested production module:

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedResolution.lean
```

If the distinguished-depth theorem belongs more naturally in an existing summit/depth module, place it there and keep the new resolution module focused on branch orchestration.

Add the facade import/export in `DkMath/FLT/Seven.lean`.

Add focused API and axiom audits following the campaign convention.

Suggested report:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-009.md
```

## 7. Hard boundaries

Do **not**:

- claim that the common summit is contradictory;
- claim that `PrimitiveRamifiedSummitPacket` cannot exist;
- inhabit `AwayCarrierReconstruction` or the U1.6 reconstruction obligation;
- infer terminal provenance from the common summit;
- infer `7 ∤ gapRoot`; the U1.6 conditional calculation should in fact give the opposite;
- treat a signed summit as a positive natural chart without its checked provenance wrapper;
- invent a recursive descent from the new normalization;
- use `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

## 8. Outcome classification

Use one of:

```text
Outcome A — PRIMITIVE SECOND-CASE CLASSIFICATION AND GLOBAL RAMIFIED
            RESOLUTION GREEN; AWAY BRANCH ABSORBED INTO COMMON SUMMIT
```

if the exact one-endpoint classification and provenance-preserving global summit resolution both kernel-check.

```text
Outcome B — SECOND-CASE CLASSIFICATION GREEN; GLOBAL RAMIFIED RESOLUTION
            STILL NEEDS A PROVENANCE/ORIENTATION BRIDGE
```

if exact endpoint classification is proved but one branch cannot be packaged into the common summit without a new honest bridge.

```text
Outcome C — GLOBAL SECOND-CASE NORMALIZATION STILL HAS A CHECKED GAP
```

if even the endpoint classification cannot be completed from the present checked surface.

## 9. Validation

At minimum run focused builds for all touched/new production modules, then:

```text
lake build DkMath.FLT.Seven
```

Add focused API and `#print axioms` audit files.  Expected inherited axiom surface remains only:

```text
[propext, Classical.choice, Quot.sound]
```

Run the campaign forbidden-source scan and `git diff --check`.

In `report-009.md`, distinguish carefully between:

- **second-case/global ramified normalization**, which this checkpoint may prove;
- **ramified summit exclusion**, which remains the actual FLT7 closure problem.
