# FLT7TC-002 — Parent provenance and p=7 coordinate orientation bridge

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

## Scope

The attached `instruction-002.md` was used as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint repairs generic packet provenance and selects the shortest
honest p=7 parent surface.  It does not identify arbitrary QR/QNR packets with
the specialized packet, enter the away branch, or claim a ramified
contradiction.

## 1. Generic parent provenance

`PrimeTraceOneStrippedIdealPacket` now retains the constructor provenance:

```lean
parent_eq_coord :
  parent = P.coord (g + u : ℤ) (u : ℤ)
```

The field is populated in
`DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean` by `rfl`, because the local
constructor definition is exactly

```lean
let parent : TraceOneInt (signedPrimeParameter p) :=
  P.coord (g + u : ℤ) (u : ℤ)
```

The API audit proves this for an arbitrary packet `Q` by applying
`Q.parent_eq_coord`.  No norm equality, axis equality, or uniqueness of
TraceOne representations is used.

## 2. p=7 canonical/orientation bridge audit

No canonical p=7 `PrimeTraceOneCoordinatePacket` was constructed.  The current
QR/QNR API exposes the packet fields `RZ`, `SZ`, `AZ`, `map_RZ`, `gauss_form`,
`gauss_difference`, `half_relation`, and `norm_eq`, but it provides no checked
theorem relating the evaluated `AZ/SZ` pair to
`cyclotomicSevenToTraceOne` at p=7.

The specialized object is independently defined in
`DkMath/FLT/Seven/QuadraticBridge.lean` by the explicit cubic pair
`cyclotomicSevenFst`/`cyclotomicSevenSnd`.  The available generic compatibility
is only a norm/shell identity.  Since equality of norms does not imply element
equality, sign, or conjugation, no finite orientation relation was promoted.
No theorem in this checkpoint identifies an arbitrary `P.coord` with the
specialized coordinate.

This is the exact QR/QNR obstruction: the pinned generic packet fields prove
the abstract Gauss/norm API, while the specialized cubic coordinates are not
connected to those fields by an element-level provenance theorem.  Building a
canonical packet would require a new p=7 field-level construction rather than
a local normalization.

## 3. Specialized parent surface and natural witnesses

The nearest honest p=7 parent source is the existing
`SevenQuadraticSeventhPowerPacket`.  Its checked field

```lean
coordinate_eq :
  cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) =
    sevenAxis * root ^ 7
```

already supplies the parent/root relation needed by the direct ramified
obstruction.  The corresponding residual relation is retained separately as
`residual_eq`; it is not silently identified with a generic `Q.residual`.

The specialized `SevenAdicPowerSplit` and generic `PrimeAdicPowerSplit` expose
matching equations:

```text
z - y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
```

and their p=7 generic forms.  The construction
`nonempty_sevenAdicPowerSplit_of_packet` copies witnesses from one generic
split into a specialized split, but the public noncomputable choice functions
do not provide an equality theorem identifying arbitrary witness pairs.  Thus
the current checked result is matching equations, not witness identity.

## 4. Generic versus specialized residuals

No theorem identifies `Q.residual` with
`SevenQuadraticResidualPacket.residualCore`.  Their seventh-power norm data and
axis equations are insufficient for such an identification, and no
choice-uniqueness principle was introduced.  Any later cancellation argument
must first provide the exact parent and axis hypotheses in a common carrier.

## 5. Architectural conclusion

The generic p=7 route now contributes a real API repair: every stripped packet
retains its parent provenance, and FLT7TC-001 supplies the generic residual
seventh-power/unit facts.  It does not add a new specialized ramified parent
invariant beyond the existing `SevenQuadraticSeventhPowerPacket`, which already
has the exact cyclotomic parent/root equation.  Rebuilding that same equation
through the generic QR/QNR layer would add substantial theory without a new
obstruction datum.

Therefore the direct ramified attack should consume:

1. the existing `SevenQuadraticSeventhPowerPacket.coordinate_eq` and
   `residual_eq`;
2. `SevenAdicPowerSplit` and its checked natural-number equations;
3. the shallow p=7 coordinate/unit lemmas exposed by FLT7TC-001;
4. `PrimeTraceOneStrippedIdealPacket.parent_eq_coord` only when a future
   generic-to-specialized bridge supplies a common parent carrier.

## 6. Validation

Focused builds completed successfully:

```text
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Prime
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealAxiomAudit
lake build DkMathTest.FLT.Seven.PrimeTraceOneParentSurfaceApiAudit
```

The new provenance projection appears in the axiom audit with only the
ordinary inherited foundational dependencies (`propext`, `Classical.choice`,
and `Quot.sound`).  No project axiom, `sorryAx`, `admit`, or unsafe proof was
added.  Fresh-source forbidden-construct scans over the modified Lean files
found no forbidden declaration; audit `#print axioms` commands were treated as
inspection commands.

`git diff --check` completed without diagnostics.

## Outcome

**Outcome B — GENERIC PARENT PROVENANCE GREEN; SPECIALIZED PACKET IS THE
HONEST P=7 PARENT SOURCE**.
