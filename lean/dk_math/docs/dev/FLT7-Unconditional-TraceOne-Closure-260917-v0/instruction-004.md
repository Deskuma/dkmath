# FLT7TC-004 — Direct specialized-packet to primitive ramified summit bridge

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint follows:

```text
FLT7TC-003: Outcome B
SHALLOW RAMIFIED DEPTH PACKAGE GREEN;
NO DIRECT CONTRADICTION;
OLD SUMMIT BRIDGE IS THE NEXT HONEST FRONTIER
```

Treat the following facts as fixed input:

```text
SevenQuadraticSeventhPowerPacket x y z
  -> exact ramified p=7 power split
  -> cyclotomicSevenToTraceOne z y = sevenAxis * root^7
  -> norm root = b
  -> 7 ∤ norm root
  -> 7^5 ∣ root.snd
```

The direct shallow constraints are arithmetically consistent and do not by
themselves imply `False`.

The purpose of FLT7TC-004 is therefore to connect the current specialized
quadratic packet directly to the already existing historical common ramified
summit **without** replaying the old terminal Row-Y / Row-Z route.

The key target is:

```text
SevenQuadraticSeventhPowerPacket
        ↓ direct adapter
PrimitiveRamifiedSummitPacket
        ↓ existing historical theorems
exact ramified depth / primitive root arithmetic / shallow routing facts
```

This is a bridge/reuse checkpoint.  It is not a license to import the entire
historical fusion/degree-six tower or to claim a contradiction merely because
the summit is inhabited.

## 1. Read first

Before editing, inspect at minimum:

```text
DkMath/FLT/Seven/PrimeTraceOneRamifiedObstruction.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
DkMath/FLT/Seven/QuadraticResidualPacket.lean
DkMath/FLT/Seven/SevenAdicPowerSplit.lean
DkMath/FLT/Seven/PrimitiveCoordinateCoprime.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedRouting.lean
```

Also read:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-003.md
DkMath/FLT/Seven/docs/STATUS.md
```

Inspect further historical ramified modules only as needed to answer the
reachability audit in §7.  Do not infer signatures from this instruction when
the source gives the exact API.

## 2. Dependency boundary

Add a small specialized bridge module.  Suggested path:

```text
DkMath/FLT/Seven/PrimeTraceOneRamifiedSummitBridge.lean
```

A reasonable dependency direction is:

```text
PrimeTraceOneRamifiedObstruction
SevenBaseTerminalRamifiedSummit
SevenBaseTerminalRamifiedDepth
(optional shallow ramified routing module)
        ↓
PrimeTraceOneRamifiedSummitBridge
```

Do not move `PrimitiveRamifiedSummitPacket` or refactor the old tower merely to
make the import graph prettier in this checkpoint.

Do not make a generic `DkMath.FLT.Prime` module depend on the historical FLT7
summit.

Export the new bridge from `DkMath.FLT.Seven` only after the focused build is
green.

## 3. Direct summit adapter

Construct a direct adapter from an arbitrary specialized packet:

```lean
p : SevenQuadraticSeventhPowerPacket x y z
```

to:

```lean
PrimitiveRamifiedSummitPacket
```

Prefer a deterministic `def`/theorem-level constructor rather than a new
choice/existence layer when all fields are already present.

A name such as

```text
SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
```

or a repository-conventional equivalent is appropriate.

The intended field assignment is:

```text
endpointLeft  := z
endpointRight := y
distinguished := x
gapRoot       := p.residual.powerSplit.a
residualRoot  := p.residual.powerSplit.b
root          := p.root
```

Use the actual source APIs for every proof field.

### Required field provenance

The adapter must fill the summit fields honestly from the packet's existing
counterexample/split data.

Expected sources include conceptually:

```text
s := p.residual.powerSplit
source := s.sevenAdic.counterexample

s.a_pos
s.b_pos
s.gap_eq
s.residual_eq
s.distinguished_eq
s.seven_not_dvd_b
source.hx / source.hy / source.hz / source.hEq
coprime_y_z_of_counterexamplePack source
counterexample_cyclotomicSeven_coordinates_isCoprime source
s.sevenAdic.seven_not_dvd_y
p.coordinate_eq
p.root_norm_eq
```

Do not add any new hypothesis to the adapter unless the existing packet truly
lacks a required summit field.

## 4. Exact cyclotomic residual equality

One summit field requires the integer identity conceptually:

```text
cyclotomicSeven (z : ℤ) (y : ℤ)
  = 7 * (s.b : ℤ)^7
```

Prove this from the existing natural split

```text
s.residual_eq : GN 7 (z-y) y = 7 * s.b^7
```

and the already checked GN/cyclotomic norm bridge.

The intended route is the same mathematical identity already used in the old
ramified summit constructors:

```text
GN_seven_sub_eq_traceOneNorm_negTwo
cyclotomicSeven_eq_traceOneNorm_negTwo
```

with the checked order fact `y ≤ z` obtained from the original positive
counterexample.

Use exact casts / `exact_mod_cast` as supported by the current source.
Do not re-expand the six-degree cyclotomic polynomial unless the existing API
forces it.

## 5. Fermat and primitive endpoint fields

The summit's signed Fermat form should come directly from the original
counterexample:

```text
(z : ℤ)^7 - (y : ℤ)^7 = (x : ℤ)^7
```

Do not introduce a new Fermat equation or a permuted counterexample merely to
populate the structure.

Likewise:

```text
endpoint_coprime
endpointLeft_ne_zero
endpointRight_ne_zero
endpointSum_ne_zero
coordinate_coprime
endpointRight_not_seven_dvd
```

must be derived from the existing original orientation `(x,y,z)` carried by
the specialized packet.

For `endpointSum_ne_zero`, positivity is sufficient.  Do not over-engineer an
arithmetic classification.

## 6. Pull the historical exact depth theorem back to the current packet

After the direct summit adapter is checked, expose the exact historical depth
formula directly on `SevenQuadraticSeventhPowerPacket`.

Target content:

```lean
padicValNat 7 (Int.natAbs p.root.snd) =
  5 + 7 * padicValNat 7 p.residual.powerSplit.a
```

Use the existing theorem

```text
PrimitiveRamifiedSummitPacket.rootSnd_padicValNat
```

through the adapter.  Do not reprove the historical ramified-gap expansion or
valuation algebra in this checkpoint.

This theorem should make explicit that FLT7TC-003's result

```text
7^5 ∣ p.root.snd
```

was a shallow consequence of the stronger exact formula, not an independent
contradiction.

If cheap, also expose one or two high-value summit facts back on the specialized
packet, for example:

```text
IsCoprime p.root.fst p.root.snd
7 ∣ p.root.snd
```

by reusing the old summit/routing API.  These are optional unless needed for
§7.  Do not duplicate their proofs.

## 7. Historical tower reachability audit

This is the second central deliverable.

Once the direct summit exists, determine **exactly how far the old ramified
tower can be entered using only `PrimitiveRamifiedSummitPacket`**.

Inspect the actual module dependency/API surface and classify downstream
results into at least these groups:

```text
A. pure-summit consumers
   need only PrimitiveRamifiedSummitPacket

B. summit + cheaply derivable structure
   e.g. routing/coprimality packets constructible from summit alone

C. provenance-sensitive consumers
   require TerminalPrimitiveRamifiedSummitPacket,
   Row-Y/Row-Z label, terminal carrier, away routing state, or another object
   not reconstructible from the new specialized packet without new work

D. heavy fusion / degree-six / reconstruction frontier
   intentionally outside this checkpoint
```

The report must name the **deepest honest reusable endpoint** reached from the
new direct adapter without manufacturing missing terminal provenance.

Also name the **first exact downstream type/theorem whose input is not
available** from the specialized packet + pure summit API.

Do not merely say “the old tower is reachable”.  Pin the exact boundary.

## 8. Important architectural question

Answer explicitly in `report-004.md`:

```text
Does the direct SevenQuadraticSeventhPowerPacket -> PrimitiveRamifiedSummitPacket
adapter bypass a historical missing provider, or does it only bypass the old
route used to construct data that was already available from an actual
ramified counterexample?
```

Distinguish these possibilities carefully.

A bridge that shortens the entry path is useful even if it does not solve the
historical U1.6 reconstruction obligation.

Do **not** claim that the old `InternalDepthFourCounterexampleReconstructionObligation`
is solved unless an actual inhabitant is constructed with the exact expected
type.

## 9. Preferred production surface

At minimum, aim for a small public API equivalent to:

```text
SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
SevenQuadraticSeventhPowerPacket.rootSnd_padicValNat_exact
```

Names may follow current conventions.

If exposing root-coordinate primitivity is clean through the historical API,
an additional theorem is welcome:

```text
SevenQuadraticSeventhPowerPacket.root_coordinates_isCoprime
```

but avoid name collisions with existing methods and avoid pulling in a much
deeper module solely for cosmetic convenience.

## 10. Do not conflate roots or witnesses

The direct summit must use:

```text
root := p.root
gapRoot := p.residual.powerSplit.a
residualRoot := p.residual.powerSplit.b
```

Do not choose new roots or reconstruct independent seventh-power witnesses.
The value of this bridge is that the **same root and same natural split
witnesses** cross into the historical summit.

If a proof unexpectedly requires a fresh `Classical.choose`, stop and inspect
whether the packet already retains the needed witness.

## 11. Tests and audits

Add focused tests, for example:

```text
DkMathTest/FLT/SevenPrimeTraceOneRamifiedSummitBridgeApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOneRamifiedSummitBridgeAxiomAudit.lean
```

The API audit should pin at least:

```text
direct specialized packet -> PrimitiveRamifiedSummitPacket
same root preserved
same gapRoot preserved
same residualRoot preserved
exact root.snd padicValNat formula
```

If optional primitive-root coordinate facts are exposed, pin those too.

The axiom audit should `#print axioms` representative public bridge theorems.
No new project axiom, `sorryAx`, `sorry`, `admit`, or unsafe declaration is
allowed.

## 12. Validation

At minimum run the focused targets actually touched by the implementation.
Expected targets include conceptually:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction
lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedSummitBridgeApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedSummitBridgeAxiomAudit
git diff --check
```

If the bridge imports a shallow routing module for a public corollary, include
that target as well.

Scan all newly edited production/test Lean files for fresh declarations using:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Treat intentional `#print axioms` commands as audits, not forbidden project
axioms.

## 13. Report

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-004.md
```

The report must record:

1. exact files changed;
2. exact adapter theorem/definition signature;
3. how every `PrimitiveRamifiedSummitPacket` field is sourced;
4. whether the same `root`, `a`, and `b` witnesses are preserved definitionally
   or by checked equalities;
5. whether the exact historical root second-coordinate depth formula is now
   available directly from `SevenQuadraticSeventhPowerPacket`;
6. comparison with FLT7TC-003's weaker `7^5 ∣ root.snd` theorem;
7. the pure-summit historical reachability classification from §7;
8. the deepest honest reusable historical endpoint;
9. the first exact missing downstream input;
10. whether this bridge changes the status of the historical
    `InternalDepthFourCounterexampleReconstructionObligation`;
11. focused build / axiom / forbidden-source / whitespace results.

Update `ROADMAP.md` after validation:

```text
FLT7TC-003: completed — Outcome B
FLT7TC-004: completed — <actual outcome>
```

Choose the next current checkpoint based on the actual result:

- if the bridge reaches a useful historical ramified endpoint but no
  contradiction, record the exact next focused ramified frontier before
  automatically switching to the away branch;
- if the bridge only confirms that the old ramified route adds no new closure,
  make FLT7TC-005 (away branch) current;
- if an actual ramified contradiction is obtained, record that fact precisely
  and then make FLT7TC-005 current.

## 14. Outcome classification

Use exactly one of:

```text
Outcome A — DIRECT SPECIALIZED PACKET -> PRIMITIVE RAMIFIED SUMMIT BRIDGE GREEN;
            HISTORICAL EXACT DEPTH RECOVERED

Outcome B — SUMMIT BRIDGE GREEN; HISTORICAL PURE-SUMMIT ROUTE REACHES A NEW
            PRECISE FRONTIER BUT NO CONTRADICTION

Outcome C — PACKET DATA NEARLY MATCH SUMMIT; ONE EXPLICIT SUMMIT FIELD OR
            CAST/ORIENTATION BRIDGE REMAINS MISSING
```

`Outcome A` means the adapter and exact depth pullback are kernel-checked.  If
the reachability audit additionally identifies a new nontrivial downstream
frontier, it is acceptable to report `Outcome B` instead to emphasize that
architectural result.

Neither A nor B means FLT7 is proved.

## Hard boundaries

Do **not** in FLT7TC-004:

- replay the old terminal Row-Y/Row-Z construction in order to build the
  summit;
- replace the current specialized packet root with a newly chosen root;
- identify generic QR/QNR residuals with specialized residuals;
- infer a contradiction from the exact depth formula alone;
- claim that `7^5 ∣ root.snd` and `7 ∤ norm root` are inconsistent;
- manufacture `TerminalPrimitiveRamifiedSummitPacket` without its actual
  terminal provenance fields;
- claim the U1.6 reconstruction obligation is inhabited without constructing
  the exact required object;
- open a degree-six / real-cubic / global-oriented factorization implementation
  unless a small read-only audit is needed to identify the boundary;
- introduce a recursive descent or well-founded decrease;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The desired result is a **minimal direct entry bridge into the historical
ramified arithmetic**, plus an exact audit of how much of that arithmetic can
be reused from the new route.
