# FLT7TC-002 — Parent provenance and p=7 coordinate orientation bridge

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint follows the completed FLT7TC-001 implementation recorded in
`report-001.md`.

Treat the following as fixed checked input:

```text
FLT7TC-001: Outcome A

For every existing p=7 generic stripped packet Q:

- Q.residual reaches explicit seventhPowerFst / seventhPowerSnd coordinates;
- Q.residual is an exact seventh power;
- the same exact seventh-power root has norm prime to 7;
- 7 | Q.residual.snd;
- 7 ∤ seventhPowerSndCore(root.fst, root.snd);
- 49 | Q.residual.snd ↔ 7 | root.snd.
```

The unresolved boundary is the **parent**.

There are two logically separate provenance questions:

```text
A. Q.parent = P.coord (g+u) u

B. for p=7, how does P.coord z y relate to
   cyclotomicSevenToTraceOne z y ?
```

FLT7TC-000 established that A is true in the constructor implementation but is
not retained by the packet type, while B is not proved by the present generic
API.  Do not merge these two problems.

The purpose of FLT7TC-002 is to repair A unconditionally and then determine the
**smallest honest p=7 bridge** needed for B.  It is acceptable for B to end in a
precise frontier if the current QR/QNR packet is genuinely too noncanonical.

## 1. Read first

Before editing, inspect at minimum:

```text
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
DkMath/FLT/Prime/PrimeTraceOneCoordinateCoprime.lean
DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean
DkMath/FLT/Seven/QuadraticBridge.lean
DkMath/FLT/Seven/QuadraticResidualPacket.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
DkMath/FLT/Seven/PrimeTraceOneClosureBridge.lean
DkMath/FLT/Seven/SevenAdicPowerSplit.lean
```

Also read:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-000.md
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-001.md
```

Audit exact current theorem names and import directions before changing any
production module.

## 2. First close the generic packet provenance loss

`PrimeTraceOneStrippedIdealPacket` currently stores an arbitrary field

```lean
parent : TraceOneInt (signedPrimeParameter p)
```

and the constructor locally defines

```lean
parent := P.coord (g + u : ℤ) (u : ℤ)
```

but the equality is not retained in the structure.

This is an API/provenance defect, not new mathematics.

### Preferred repair

Add a field with content equivalent to:

```lean
parent_eq_coord :
  parent = P.coord (g + u : ℤ) (u : ℤ)
```

or the orientation-equivalent equality if repository conventions prefer the
reverse direction.

Populate it directly in
`nonempty_primeTraceOneStrippedIdealPacket` from the local definition of
`parent`.

Do not prove it from `axis_eq`, norm equality, or uniqueness of representations.
It should come from construction provenance.

### Compatibility audit

Search all structure literals / consumers of `PrimeTraceOneStrippedIdealPacket`
and update only what the new field genuinely requires.

If changing the structure would cause a disproportionately broad source break,
an alternative is acceptable only if it gives **every production packet Q** an
equally strong checked theorem recovering the same equality.  A theorem about
only one noncomputable choice without proving the property of arbitrary Q is
not equivalent and should not be presented as such.

After this step the following must be kernel-checked for arbitrary Q:

```text
Q.parent = P.coord (g+u) u.
```

## 3. Do not try to identify arbitrary `P` from norm equality

The present packet supplies

```text
P.coord_norm_eq z y
```

but

```text
norm (P.coord z y) =
norm (cyclotomicSevenToTraceOne z y)
```

is **not** enough to conclude element equality, equality up to sign, or equality
up to conjugation.

No theorem in this checkpoint may use equality of norms as an element
identification principle.

## 4. Audit the shortest p=7 bridge strategy before implementing it

There are three possible strategies.  Prefer them in this order only after
checking the current source.

### Route A — canonical p=7 coordinate packet

If the QR/QNR polynomial API allows it without a large new theory layer, build a
p=7 `PrimeTraceOneCoordinatePacket` whose evaluated coordinates are the existing
specialized cubic coordinates.

The desired endpoint is conceptually:

```lean
P7.coord z y = cyclotomicSevenToTraceOne z y
```

for a checked p=7 packet `P7`.

It is sufficient for the FLT7 campaign to construct such a **canonical p=7
packet**.  Do not prove that every arbitrary `PrimeTraceOneCoordinatePacket`
coincides with it unless uniqueness falls out cheaply.

The likely polynomial candidates are determined by the specialized formulas:

```text
A7(z,y) = cyclotomicSevenFst z y
S7(z,y) = cyclotomicSevenSnd z y
R7       = 2*A7 + S7.
```

At polynomial level these correspond to

```text
A7 = z^3 + z^2*y - y^3
S7 = -z^2*y - z*y^2
R7 = 2*z^3 + z^2*y - z*y^2 - 2*y^3.
```

Do not merely define these and assert they form a packet.  The packet fields
`map_RZ`, `gauss_form`, `gauss_difference`, `half_relation`, and `norm_eq` must
all be kernel-checked against the current `Rpoly`, `Dpoly`, and
`quadraticGauss` API.

Before promoting anything to production, use a focused scratch/test proof to
determine whether these identities are realistically available from the
pinned APIs.

### Route B — prove only the orientation relation actually needed

If exact canonical packet construction is unnecessarily strong, determine
whether the generic provenance fields force an explicit relation such as

```text
P.coord z y = cyclotomicSevenToTraceOne z y
P.coord z y = conj (cyclotomicSevenToTraceOne z y)
P.coord z y = -cyclotomicSevenToTraceOne z y
P.coord z y = -conj (cyclotomicSevenToTraceOne z y)
```

or another finite orientation relation.

Such a theorem must be derived from the retained `RZ/SZ/AZ`, `map_RZ`,
`gauss_difference`, and `half_relation` provenance, not merely from the norm.

If only a finite orientation class can be proved, also state exactly which
properties needed later are invariant under that orientation.

### Route C — use the existing specialized packet instead of duplicating it

The existing specialized route already has:

```lean
SevenQuadraticResidualPacket.coordinate_eq :
  cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) =
    sevenAxis * residualCore
```

and

```lean
SevenQuadraticSeventhPowerPacket.coordinate_eq :
  cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) =
    sevenAxis * root ^ 7.
```

If Route A/B would merely rebuild this existing fact through a much heavier
QR/QNR proof, stop and say so.

In that case, the correct result of FLT7TC-002 is:

1. generic `Q.parent` provenance repaired;
2. arbitrary generic `P` remains noncanonical at element level;
3. the **nearest honest p=7 parent source for the direct obstruction is the
   existing specialized `SevenQuadraticSeventhPowerPacket`**;
4. FLT7TC-003 should consume that packet together with the shallow arithmetic
   exposed by FLT7TC-001, rather than force an artificial generic/specialized
   equality.

This is a valid and useful Outcome B.  Do not inflate Route A into a large
cyclotomic subproject merely for architectural symmetry.

## 5. Compare the generic and specialized natural-number front ends

Record the exact checked compatibility between the specialized ramified input
and the generic p=7 packet.

At minimum pin:

```lean
SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket :
  PrimeAdicFactorPacket 7 (z-y) y x
```

and compare the `PrimeAdicPowerSplit` fields with the existing
`SevenAdicPowerSplit` fields.

Determine whether the two routes already use the same natural witnesses
`a,b`, or merely prove existence of witnesses with the same equations.

Do not identify existential witnesses unless a checked theorem or structure
projection does so.

This comparison is important for deciding whether a generic residual and a
specialized `residualCore` can honestly be identified later.

## 6. If a canonical p=7 packet is achieved, compose the parent theorem

Only if Route A or B is kernel-checked, expose a p=7 theorem that combines the
new generic packet provenance with the specialized coordinate relation.

A desirable canonical statement is conceptually:

```lean
Q.parent = cyclotomicSevenToTraceOne (g+u : ℤ) (u : ℤ)
```

for Q built over the canonical p=7 coordinate packet.

For an actual ramified FLT7 counterexample the parameters specialize to

```text
g = z-y
u = y
(g+u : ℤ) = z
```

only after using the checked `y ≤ z` / cast normalization already present in
the specialized route.  Do not silently rewrite natural subtraction through
integer casts without the required inequality.

If the available relation is sign/conjugation rather than exact equality,
preserve it explicitly in the theorem type.

## 7. Do not conflate generic and specialized residuals

Even after the parent coordinate is identified, these two residual objects are
not automatically equal:

```text
Q.residual
SevenQuadraticResidualPacket.residualCore.
```

Both may satisfy

```text
parent = sevenAxis * residual
```

only after suitable orientation/provenance bridges.  Equality may then follow
from cancellation if the exact hypotheses are present, but it must be proved.

Do not infer residual equality from equal norms or from the fact that both are
seventh powers.

If a clean cancellation theorem yields equality once the parents agree, record
it.  Otherwise leave residual identification for FLT7TC-003.

## 8. Important architectural observation to record

The specialized FLT7 route already reaches a stronger parent statement than
the generic route:

```text
cyclotomicSevenToTraceOne z y = sevenAxis * root^7.
```

Therefore this checkpoint must explicitly answer:

> Does the generic TraceOne route provide any new ramified information beyond
> the existing specialized `SevenQuadraticSeventhPowerPacket`, once p=7 is
> fixed?

Possible honest answers include:

```text
- yes: it supplies a genuinely new invariant needed by FLT7TC-003;
- no: it reconstructs the same quadratic endpoint through a cleaner generic
  route, and the direct-obstruction search should use the specialized packet;
- partially: one side has stronger natural-number data while the other has
  stronger coordinate provenance.
```

This comparison is required in `report-002.md`.  It determines the next attack
rather than being mere documentation.

## 9. Production placement

The generic provenance repair belongs with the generic packet, preferably:

```text
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
```

Any p=7-only adapter belongs in the specialized FLT7 layer, near:

```text
DkMath/FLT/Seven/PrimeTraceOneClosureBridge.lean
```

or a new narrowly named sibling module if the content is materially distinct.

Do not put p=7-specific polynomial identities into neutral
`DkMath.Lib.NumberTheory`.

Do not make `DkMath.FLT.Prime` import the specialized FLT7 bridge.

## 10. Tests and audits

Add/update focused API tests for the generic parent provenance field/theorem.

If a p=7 canonical/orientation bridge is promoted, add a specialized API audit
for it as well.

Representative axiom audits must cover any new public theorem that depends on
nontrivial cyclotomic provenance.

Expected foundational dependencies remain the ordinary existing surface such
as:

```text
propext
Classical.choice
Quot.sound
```

as applicable.  A new project axiom, `sorryAx`, `admit`, or unsafe proof is a
failure.

Run a fresh-source scan over every production/test Lean file modified in this
checkpoint for:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Distinguish comments and `#print axioms` commands from actual declarations.

## 11. Validation

At minimum rebuild all modules directly affected by the structure/API change.
The exact set depends on the compatibility fallout, but should include at least
conceptually:

```text
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven
```

plus all new/updated API and axiom audits.

Because `PrimeTraceOneStrippedIdealPacket` is a central structure, also build
the public generic facade if the field is added:

```text
lake build DkMath.FLT.Prime
```

Run:

```text
git diff --check
```

## 12. Required report

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-002.md
```

It must state clearly:

1. whether arbitrary `Q.parent = P.coord (g+u) u` is now retained and checked;
2. exact source change used to preserve that provenance;
3. whether a canonical p=7 coordinate packet was built;
4. if yes, exact theorem relating its `.coord` to
   `cyclotomicSevenToTraceOne`;
5. if no, the exact QR/QNR theorem/API obstruction encountered;
6. whether a finite sign/conjugation/orientation relation was proved instead;
7. whether generic and specialized natural `a,b` witnesses are actually the
   same or merely satisfy matching equations;
8. whether generic `Q.residual` and specialized `residualCore` can be identified
   without an unproved choice-uniqueness principle;
9. whether the generic p=7 route adds any new ramified invariant beyond the
   existing specialized quadratic seventh-power packet;
10. exact builds, axiom output, and forbidden-source scan results;
11. the precise recommended input surface for FLT7TC-003.

Update `ROADMAP.md` only after validation:

```text
FLT7TC-001: completed — Outcome A
FLT7TC-002: completed — <actual outcome>
FLT7TC-003: current
```

Do not mark FLT7TC-003 current until the report identifies an honest parent
surface to consume.

## 13. Outcome classification

Use exactly one of:

```text
Outcome A — GENERIC PARENT PROVENANCE + CANONICAL P=7 COORDINATE BRIDGE GREEN
Outcome B — GENERIC PARENT PROVENANCE GREEN; SPECIALIZED PACKET IS THE HONEST P=7 PARENT SOURCE
Outcome C — GENERIC PARENT PROVENANCE GREEN; P=7 ORIENTATION REMAINS A SEPARATE CYCLOTOMIC FRONTIER
```

### Outcome A requires

- arbitrary generic Q retains `Q.parent = P.coord (g+u) u`;
- a checked canonical/orientation p=7 bridge reaches
  `cyclotomicSevenToTraceOne` at element level;
- no norm-equality shortcut is used;
- focused builds and axiom audits are green.

### Outcome B is preferred over forcing A when

- the specialized `SevenQuadraticSeventhPowerPacket` already supplies exactly
  the parent/root relation needed for FLT7TC-003;
- rebuilding the same fact through generic QR/QNR coordinates would add
  substantial theory but no new obstruction data.

### Outcome C is appropriate when

- generic packet provenance is repaired;
- the remaining orientation problem is mathematically substantive and cannot
  be reduced to the already specialized packet without losing a needed new
  generic invariant.

## Hard boundaries

Do **not** in FLT7TC-002:

- infer equality of TraceOne elements from equality of norms;
- assert every `PrimeTraceOneCoordinatePacket` at p=7 is canonical without a
  checked uniqueness theorem;
- identify existential `PrimeAdicPowerSplit` witnesses with specialized
  `SevenAdicPowerSplit` witnesses by matching formulas alone;
- identify `Q.residual` with `residualCore` merely because both have seventh
  power norms;
- rebuild the entire QR/QNR/Gauss theory only to reproduce an already available
  specialized parent equality unless the new route gives a concrete new
  invariant;
- import an FLT7 terminal contradiction theorem;
- claim the ramified branch is contradictory;
- touch the away branch;
- use `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The purpose of this checkpoint is to establish **honest provenance and choose
the shortest noncircular parent surface for the direct ramified obstruction**.