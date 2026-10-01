# FLT7TC-003 — Direct ramified seventh-power obstruction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint follows:

```text
FLT7TC-000  Outcome B — p=7 endpoint audited; parent provenance frontier found
FLT7TC-001  Outcome A — explicit seventh-power / same-root 7-unit bridge green
FLT7TC-002  Outcome B — generic parent provenance repaired; specialized
                         SevenQuadraticSeventhPowerPacket selected as the
                         honest p=7 parent source
```

The purpose of FLT7TC-003 is to determine whether the **existing specialized
quadratic p=7 packet**, together with the shallow seventh-power arithmetic now
exposed by FLT7TC-001, already yields a direct contradiction in the ramified
branch.

Do not enter the historical real-cubic / degree-six fusion machinery in this
checkpoint.  If the shallow quadratic data are arithmetically consistent,
stop and identify the exact next bridge for FLT7TC-004.

## 1. Read first

Inspect at minimum:

```text
DkMath/FLT/Seven/QuadraticResidualPacket.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
DkMath/FLT/Seven/CoordinateNormalForm.lean
DkMath/FLT/Seven/SeventhPowerCoordinates.lean
DkMath/FLT/Seven/PrimeTraceOneClosureBridge.lean
DkMath/FLT/Seven/SevenAdicPowerSplit.lean
DkMath/FLT/Seven/QuadraticBridge.lean
DkMath/FLT/Seven/AxisDivisibility.lean
```

Also inspect, **as reference only unless a shallow import is genuinely
necessary**:

```text
DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean
DkMath/FLT/Seven/docs/STATUS.md
```

Read the current campaign reports:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-001.md
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-002.md
```

Treat source declarations as authoritative.  Do not infer theorem signatures
from this instruction if the current API differs.

## 2. Use the specialized ramified packet as the parent source

For this checkpoint the principal input is the existing specialized packet:

```lean
packet : SevenQuadraticSeventhPowerPacket x y z
```

with its checked data, including conceptually:

```text
packet.residual.powerSplit
packet.residual.residualCore
packet.residual.coordinate_eq
packet.residual.residual_terminal
packet.residual.residual_norm_not_seven_dvd
packet.residual.residual_norm_eq
packet.root
packet.residual_eq : residualCore = root^7
packet.coordinate_eq :
  cyclotomicSevenToTraceOne z y = sevenAxis * root^7
```

Do not identify this residual with an arbitrary generic
`PrimeTraceOneStrippedIdealPacket.residual`.

Do not attempt to construct a canonical p=7 `PrimeTraceOneCoordinatePacket`.
FLT7TC-002 already determined that this is not the shortest honest path.

## 3. Pin the exact natural p=7 split

Expose or reuse the specialized split data from
`packet.residual.powerSplit`:

```text
z - y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
x = 7*a*b
0 < a
0 < b
Coprime a b
7 ∤ b
```

Record the exact field names in `report-003.md`.

The direct obstruction must use actual checked split data rather than only the
weak statement `7 ∣ z-y`.

## 4. Root norm: identify the shallow exact theorem surface

From

```text
packet.residual_eq : residualCore = root^7
packet.residual.residual_norm_eq : norm residualCore = b^7
```

and positivity/nonnegativity of the `TraceOneInt (-2)` norm, determine whether
the shallow current API already proves, or can cheaply prove:

```text
norm packet.root = b
```

and therefore

```text
¬ (7 : ℤ) ∣ norm packet.root.
```

Prefer reusing an existing theorem if one is available at a shallow import
boundary.  If the only existing proof is private inside the historical summit
module, a small local/public helper is acceptable **only if it is genuinely
neutral p=7 quadratic arithmetic and does not pull in the old terminal tower**.

Do not duplicate a large proof merely to change module ownership.

## 5. Explicit parent coordinate equations

Construct or reuse the shallow ramified coordinate normal form:

```text
cyclotomicSevenFst z y
  = ramifiedSeventhFst root.fst root.snd

cyclotomicSevenSnd z y
  = ramifiedSeventhSnd root.fst root.snd
```

The existing `RamifiedCoordinateNormalForm` may already be the correct
consumer surface.

Also retain the exact elementary identity

```text
cyclotomicSevenSnd z y = -z*y*(z+y)
```

when useful.  Do not replace an existing checked formula with an informal
factorization.

## 6. Test the mod-7 surface before searching for a contradiction

Combine the ramified split and primitive endpoint information with the
existing characteristic-seven formulas:

```text
ramifiedSeventhFst_mod_seven
ramifiedSeventhSnd_mod_seven
traceOneNorm_mod_seven_eq_linear_sq
```

Determine exactly what follows for

```text
root.fst + 4*root.snd  (mod 7)
```

and compare it with the endpoint residue sector of the ramified branch.

Important: a nonzero relation here is expected to be **compatible** with the
root norm being prime to 7.  Do not declare a contradiction merely because
both sides have constrained residues.

If the complete mod-7 surface is consistent, state that explicitly in the
report before moving to higher 7-adic depth.

## 7. High-value direct depth target

The principal arithmetic experiment of this checkpoint is the second
coordinate.

Use the exact gap

```text
z - y = 7^6 * a^7
```

and the exact coordinate equation to determine the strongest shallow theorem
about the 7-adic depth of `root.snd`.

The historical ramified tower later proves the reference formula

```text
padicValNat 7 (Int.natAbs root.snd)
  = 5 + 7 * padicValNat 7 gapRoot.
```

This formula is **reference evidence, not an instruction to import the whole
historical tower and call the checkpoint solved**.

The direct quadratic investigation should answer:

1. Can the same depth formula (or a sufficient specialization of it) be
   obtained directly from the current specialized seventh-power packet with a
   shallow dependency surface?
2. Does FLT7TC-001's same-root seventh-power factorization materially shorten
   the proof?
3. Does the resulting depth statement conflict with any already checked
   primitive, norm-unit, coprimality, or natural split invariant?

A useful intermediate chain may involve the already checked fact

```text
seventhPowerSnd = 7 * root.snd * seventhPowerSndCore
```

with

```text
7 ∤ seventhPowerSndCore
```

so that the exact 7-adic depth of the seventh-power second coordinate becomes
`1 + v_7(root.snd)`.

Do not assume the historical depth formula; derive only what follows from the
chosen shallow inputs.

## 8. Search for an actual contradiction, not merely a strong formula

After obtaining the strongest shallow congruence/valuation package, test it
against all directly available constraints:

```text
root norm prime to 7
root coordinate primitivity, if available without a deep import
residual coordinate primitivity
7^6*a^7 gap shape
7*b^7 residual norm source
49-divisibility iff 7-divisibility of root.snd
endpoint coprimality / endpoint nondivisibility
ramified coordinate equations
```

A contradiction must be an actual Lean proposition ending in `False` from a
real specialized ramified packet or a primitive ramified counterexample.

Examples of things that are **not** contradictions:

```text
7 ∣ root.snd
root.snd has large 7-adic depth
root.fst is a 7-unit
root.fst + 4*root.snd is nonzero mod 7
49 ∣ (root^7).snd
```

These conditions can coexist.

If no direct contradiction follows, do not force one.  Instead identify the
strongest shallow terminal packet and the exact missing invariant.

## 9. Consistency witness / no-go audit when appropriate

If the proposed direct contradiction reduces only to a finite collection of
local root conditions, try to show that those local conditions are themselves
consistent.

This may be done by a small checked numerical/example witness when the
conditions are independent of the full Fermat parent equation.

For example, if the only surviving root-side conditions are of the conceptual
form

```text
7 ∤ norm root
7^5 ∣ root.snd
7 ∤ root.fst
7 ∤ seventhPowerSndCore root.fst root.snd
```

then a checked witness satisfying that reduced local system is valuable: it
proves that those facts alone cannot yield the terminal contradiction.

Do **not** present such a local witness as a Fermat counterexample or as a
witness to the full `SevenQuadraticSeventhPowerPacket`.

## 10. Relationship to the old ramified summit

Audit whether the specialized direct packet contains enough data to construct
or feed the existing

```text
PrimitiveRamifiedSummitPacket
```

without passing through the historical terminal-away Row-Y/Row-Z route.

Do not implement the full fallback bridge in FLT7TC-003 unless it is a trivial
one-line reuse.  The intended purpose is to determine the FLT7TC-004 entry
point if the direct contradiction fails.

In `report-003.md`, state one of:

```text
A. direct quadratic contradiction closes the ramified branch;
B. no contradiction; direct packet reaches the old PrimitiveRamifiedSummit
   surface and FLT7TC-004 should implement that bridge;
C. no contradiction; an additional invariant is needed even before the old
   summit can be reached.
```

## 11. Production module policy

If new production theorems are justified, prefer a p=7 specialized shallow
module such as:

```text
DkMath/FLT/Seven/PrimeTraceOneRamifiedObstruction.lean
```

or a more repository-consistent name discovered during implementation.

Keep the module below the historical ramified fusion tower if possible.

Do not move or duplicate large parts of
`SevenBaseTerminalRamifiedSummit.lean` merely for architecture aesthetics.
A small reusable lemma may be promoted to a shallower module if its dependency
surface is genuinely small and all downstream builds remain green.

## 12. Tests and audits

Add focused API/axiom tests for any new production module.

Pin at minimum the strongest new results actually proved, for example:

```text
root norm equality / 7-unit theorem
ramified coordinate consequence
root.snd divisibility/depth theorem
terminal contradiction, if one genuinely exists
```

Run `#print axioms` on representative public theorems.  Expected inherited
foundations are the usual Lean/Mathlib surface such as:

```text
propext
Classical.choice
Quot.sound
```

No project axiom, `sorryAx`, `sorry`, `admit`, or `unsafe` proof may be added.

Run a fresh-source forbidden construct scan and `git diff --check`.

## 13. Suggested focused builds

At minimum, adapt and run the relevant subset of:

```text
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven.CoordinateNormalForm
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Seven.SeventhPowerCoordinates
lake build DkMath.FLT.Seven
```

plus every new production/test target added by this checkpoint.

If a historical ramified module is imported only for comparison, record that
fact separately from the shallow production dependency surface.

## 14. Report

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-003.md
```

The report must state:

1. exact production/test files changed;
2. exact specialized packet used as the source;
3. exact root norm and 7-unit facts available;
4. exact mod-7 ramified coordinate consequences;
5. strongest checked root.snd divisibility/valuation theorem;
6. whether FLT7TC-001 shortened or strengthened the shallow proof;
7. whether the full shallow constraint set is contradictory;
8. any checked local consistency witness used to rule out a fake
   contradiction;
9. whether `PrimitiveRamifiedSummitPacket` is reachable directly from the
   specialized packet and the exact proposed FLT7TC-004 bridge;
10. focused build / axiom / forbidden-source results.

Update `ROADMAP.md` after successful validation:

```text
FLT7TC-002: completed — Outcome B
FLT7TC-003: completed — <actual outcome>
```

If Outcome A closes the ramified branch, mark FLT7TC-004 as unnecessary and
make FLT7TC-005 current.

If Outcome B/C leaves a ramified bridge frontier, make FLT7TC-004 current.

## 15. Outcome classification

Use exactly one of:

```text
Outcome A — DIRECT RAMIFIED QUADRATIC CONTRADICTION GREEN

Outcome B — SHALLOW RAMIFIED DEPTH PACKAGE GREEN; NO DIRECT CONTRADICTION;
            OLD SUMMIT BRIDGE IS THE NEXT HONEST FRONTIER

Outcome C — SHALLOW RAMIFIED INVARIANTS GREEN; DIRECT DEPTH/OLD-SUMMIT
            CONNECTION STILL NEEDS A NEW BRIDGE
```

Outcome A requires an actual checked contradiction from the specialized
ramified packet/counterexample, not merely a strong valuation statement.

Outcome B is the expected honest result if the new route reconstructs the
known ramified depth package but the conditions remain consistent and the
next useful step is an explicit direct bridge into `PrimitiveRamifiedSummitPacket`.

## Hard boundaries

Do **not** in FLT7TC-003:

- identify arbitrary generic `P.coord` with `cyclotomicSevenToTraceOne`;
- identify generic and specialized residuals by equality of norms;
- import the completed deep fusion/degree-six route and present an old result
  as a new direct contradiction;
- treat a large 7-adic depth as contradictory by itself;
- treat `7 ∣ root.snd` as incompatible with a 7-unit root norm;
- infer a smaller Fermat counterexample from a smaller coordinate without a
  checked reconstruction theorem;
- claim well-founded descent without an actual decreasing counterexample
  measure and constructor;
- use the historical `InternalDepthFourCounterexampleReconstructionObligation`
  as if it were inhabited;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The goal is to decide, rigorously and cheaply, whether the **quadratic ramified
surface itself** closes FLT7 or whether the proof genuinely needs the next
structural layer.
