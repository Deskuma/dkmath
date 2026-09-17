# FLT7TC-005 — Away-branch closure audit and reconstruction frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint follows FLT7TC-004 Outcome B.

Treat the following as fixed checked input:

```text
FLT7TC-004:
- SevenQuadraticSeventhPowerPacket -> PrimitiveRamifiedSummitPacket is green;
- the exact ramified root.snd depth formula is reachable directly;
- arbitrary direct ramified packets do not supply the terminal carrier data
  required by TerminalPrimitiveRamifiedSummitPacket;
- no ramified contradiction has been proved.
```

The purpose of FLT7TC-005 is to return to the honest away branch and determine
whether the generic odd-prime split added by the Prime/TraceOne campaign
actually strengthens the existing specialized FLT7 away machinery enough to
close, or materially shrink, the historical reconstruction frontier.

Do **not** assume that the generic away split is new information.  Compare it
against the existing specialized p=7 route first.

## 1. Read first

Inspect at minimum:

```text
DkMath/FLT/Prime/CounterexampleRouting.lean
DkMath/FLT/Seven/CounterexampleRouting.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
DkMath/FLT/Seven/CoordinateNormalForm.lean
DkMath/FLT/Seven/AwaySecondCoordinateLoad.lean
DkMath/FLT/Seven/AwayValuationTransfer.lean
DkMath/FLT/Seven/CubicSecondCoordinateSplit.lean
DkMath/FLT/Seven/DescentClosureAudit.lean
DkMath/FLT/Seven/docs/STATUS.md
```

Also read:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-004.md
docs/feature/FLT7-magic-core-260722/report-flt7-010.md
docs/feature/FLT7-magic-core-260722/report-flt7-011.md
```

Use current theorem names and signatures from source.  Do not infer them from
this instruction when Lean already exposes the exact API.

## 2. First task: normalize the generic p=7 away statement

The generic prime route supplies, for p=7 conceptually,

```text
¬ 7 ∣ z-y
z-y = a^7
GTail 7 1 (z-y) y = b^7.
```

The historical specialized p=7 route already supplies conceptually

```text
¬ 7 ∣ z-y
z-y = a^7
GN 7 (z-y) y = b^7.
```

Determine the exact checked relation between these two APIs.

If no reusable adapter from `CounterexamplePack` to
`PrimitivePrimeCounterexample 7` exists, add the smallest p=7 specialized
adapter at an appropriate leaf boundary.  It must preserve the same `x,y,z`
and derive the generic primitive packet only from the existing positive,
primitive FLT7 packet fields.

Then prove the strongest cheap comparison theorem supported by the APIs.  A
valid target is a proposition-level equivalence or pair of implications
between the two away power-split statements after normalizing `GTail 7 1` and
`GN 7`.

Do **not** claim equality of existential witnesses chosen independently by two
proofs.  The content to compare is the mathematical proposition, not the
identity of `Classical.choose` terms.

If the two split statements are definitionally/simp-equivalent, record that
fact with a small regression theorem rather than building duplicate
structures.

## 3. Compare information strength against the specialized quadratic route

The specialized away route already reaches an `AwayCoordinateNormalForm` with

```text
cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7
```

plus explicit first/second seventh-power coordinate equations.

Audit whether the generic natural-number pair

```text
z-y = a^7
GN/GTail = b^7
```

contains any invariant not already derivable from the current specialized
away packet.

At minimum check:

```text
AwayCoordinateNormalForm.counterexample
AwayCoordinateNormalForm.seven_not_dvd_gap
AwayCoordinateNormalForm.coordinate_eq
AwayCoordinateNormalForm.root_norm_not_seven_dvd
AwayCoordinateNormalForm.root_coordinates_isCoprime
AwayValuationTransferPacket.valuation_eq
AwayValuationTransferPacket.root_snd_depth_lt_carrier
```

Do not weaken an existing element-level seventh-power theorem to a mere norm
or natural-factor statement and then call that progress.

## 4. Re-state the actual closure obligation

The existing formal closure boundary is `AwayDescentClosureProvider`.

Its essential requirement is not merely a smaller positive natural number.
It requires a newly reconstructed primitive FLT7 counterexample and a new away
valuation-transfer packet whose exceptional carrier is exactly

```text
Int.natAbs p.normal.root.snd.
```

Pin this statement in the new audit surface.  The checkpoint must explicitly
answer:

1. Does the generic p=7 power split provide new endpoint candidates
   `nextX,nextY,nextZ`?
2. Does it provide a new FLT7 equation for those candidates?
3. Does it provide primitive/coprime hypotheses for them?
4. Does it identify the next exceptional carrier with
   `Int.natAbs root.snd`?
5. Does it preserve an away branch condition for the new packet?

A negative answer to these questions is a legitimate result and must be
reported precisely.

## 5. Attempt only the shortest honest closure route

Try to close the away branch only if the current checked data genuinely
provide the missing reconstruction.

Permitted routes include:

### Route A — direct contradiction

Derive `False` from the simultaneous seventh powers together with the existing
quadratic coordinate/root invariants.

Do not treat the existence of two seventh powers as contradictory by itself.

### Route B — direct reconstruction

Construct an actual

```text
AwayDescentClosureProvider x y z p
```

from current data, including the new primitive counterexample packet and the
exact carrier match.

If this succeeds, expose the resulting strict `padicValNat 7` descent using
the existing `away_depth_descent_of_closureProvider` theorem.

### Route C — transition to a ramified packet

If the away data canonically construct a new primitive counterexample whose
appropriate gap is divisible by 7, route it through the already checked
ramified front end and, if possible, into the FLT7TC-004 summit bridge.

This route must construct the actual counterexample.  A congruence resemblance
or a smaller integer alone is insufficient.

## 6. Preferred bounded implementation if closure does not follow

If the generic split adds no reconstruction data, add a small specialized
comparison/audit module rather than modifying the large historical away tower.

Suggested path:

```text
DkMath/FLT/Seven/PrimeTraceOneAwayClosureAudit.lean
```

Possible public theorem surface:

- p=7 adapter from `CounterexamplePack` to generic
  `PrimitivePrimeCounterexample 7`, if missing;
- generic-away split normalized to the specialized p=7 split proposition;
- theorem showing that an existing `AwayCoordinateNormalForm` already implies
  the same natural seventh-power factor split;
- a compact packet or theorem collecting both the natural split and the
  existing strict depth transfer **only if** doing so adds a useful consumer
  surface without duplicating data;
- a precise reconstruction-frontier theorem/definition reusing
  `AwayDescentClosureProvider` rather than inventing a second obligation type.

Do not alter `AwayDescentClosureProvider` merely to make it inhabitable.

## 7. Important arithmetic facts already checked

The old away tower already proves the second-coordinate load identity
conceptually

```text
y*z*(y+z) = 7 * |root.snd| * |SndCore(root)|
```

with `7 ∤ SndCore`, and the one-hot valuation transfer

```text
v7(carrier) = 1 + v7(|root.snd|).
```

Therefore

```text
v7(|root.snd|) < v7(carrier)
```

is already checked.

Do not spend this checkpoint reproving that strict depth inequality unless a
small wrapper is required for the new comparison module.

The unresolved issue is reconstruction, not the valuation calculation.

## 8. Do not conflate the ramified terminal-carrier frontier

FLT7TC-004 found that an arbitrary direct ramified packet may have

```text
v7(gap) = 6 + 7*v7(gapRoot)
```

and therefore does not automatically supply `7 ∤ gapRoot`, which is needed by
the historical terminal-carrier packet.

That is a separate ramified provenance issue.  Do not use
`TerminalPrimitiveRamifiedSummitPacket` as an assumed receiver for the away
branch unless the complete required data are actually constructed.

## 9. Tests and audits

Add focused API and axiom audits for every new public declaration.

Suggested names:

```text
DkMathTest/FLT/SevenPrimeTraceOneAwayClosureAuditApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOneAwayClosureAuditAxiomAudit.lean
```

Use repository naming conventions if a nearby layout is preferable.

The API audit should pin at minimum:

```text
generic p=7 primitive adapter, if added
generic/specialized away split comparison
specialized away element-level seventh-power dominance over the natural split
exact existing reconstruction frontier
```

If a real closure provider is constructed, audit its carrier match and strict
depth theorem explicitly.

The axiom audit must report no project axiom or `sorryAx`.  Ordinary inherited
Lean/Mathlib foundations such as

```text
propext
Classical.choice
Quot.sound
```

are acceptable as already established in this codebase.

## 10. Validation

Run at minimum the relevant focused builds, conceptually including:

```text
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMath.FLT.Seven.CounterexampleRouting
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven.CoordinateNormalForm
lake build DkMath.FLT.Seven.AwaySecondCoordinateLoad
lake build DkMath.FLT.Seven.AwayValuationTransfer
lake build DkMath.FLT.Seven.DescentClosureAudit
lake build <new production module if any>
lake build <new API audit>
lake build <new axiom audit>
lake build DkMath.FLT.Seven
```

Also run:

```text
git diff --check
```

and scan fresh/edited Lean files for new uses of

```text
sorry
sorryAx
admit
axiom
unsafe
```

Distinguish `#print axioms` inspection commands from actual declarations.

## 11. Report

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-005.md
```

The report must state:

1. the exact generic p=7 away theorem surface consumed;
2. the exact specialized away theorem surface compared against it;
3. whether `GTail 7 1` and `GN 7` normalize to the same factor here;
4. whether the new generic route adds any invariant not already available from
   `AwayCoordinateNormalForm` / `AwayValuationTransferPacket`;
5. whether a direct contradiction was found;
6. whether an `AwayDescentClosureProvider` was actually constructed;
7. if not, the exact missing field/data needed for reconstruction;
8. whether any honest transition to the ramified FLT7TC-004 summit was built;
9. exact build, axiom-audit, forbidden-source, and diff-check results.

Update `ROADMAP.md` only after validation.

## 12. Outcome classification

Use exactly one of:

```text
Outcome A — AWAY BRANCH CLOSED BY CHECKED CONTRADICTION OR RECONSTRUCTION DESCENT
```

Requires an actual contradiction or an actual `AwayDescentClosureProvider`
with checked strict descent.  A smaller integer alone is not enough.

```text
Outcome B — GENERIC P=7 AWAY SPLIT NORMALIZES TO EXISTING SPECIALIZED DATA;
            RECONSTRUCTION FRONTIER UNCHANGED
```

Use when the Prime route adds no invariant capable of filling the existing
closure provider.

```text
Outcome C — GENERIC AWAY SPLIT ADDS A NEW CHECKED BRIDGE/INVARIANT;
            CLOSURE PROVIDER STILL MISSING
```

Use only when a genuinely new invariant is proved and its relation to the
remaining reconstruction obligation is explicit.

## Hard boundaries

Do **not** in FLT7TC-005:

- identify independently chosen existential seventh-power witnesses;
- infer a new primitive counterexample from a smaller natural number alone;
- infer an FLT equation from divisibility or valuation data;
- assume `AwayDescentClosureProvider` or
  `InternalDepthFourCounterexampleReconstructionObligation` is inhabited;
- call a strict `padicValNat` drop a descent unless the next counterexample is
  constructed;
- replace the element-level specialized away theorem by a weaker norm equality;
- manufacture a terminal ramified carrier from an arbitrary summit;
- import a final FLT7 contradiction theorem circularly;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The desired result is an exact answer to whether the new generic away split
changes the historical away closure boundary.