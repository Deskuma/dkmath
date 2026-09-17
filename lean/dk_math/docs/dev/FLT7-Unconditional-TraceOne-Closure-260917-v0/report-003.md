# FLT7TC-003 — Direct ramified seventh-power obstruction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-003.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint remains below the historical ramified fusion tower and does
not identify a generic QR/QNR residual with the specialized residual core.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneRamifiedObstruction.lean`
- `DkMath/FLT/Seven.lean` (facade export)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneRamifiedObstructionApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneRamifiedObstructionAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

## 2. Specialized source packet

All new packet-level results consume exactly
`SevenQuadraticSeventhPowerPacket`.  Its existing fields provide

```text
z-y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
cyclotomicSevenToTraceOne z y = sevenAxis * root^7
residualCore = root^7
```

through `residual.powerSplit`, `residual_eq`, and `coordinate_eq`.  The
generic `PrimeTraceOneCoordinatePacket` is not used to manufacture or identify
this specialized root.

## 3. Norm and 7-unit results

The production module proves:

```lean
SevenQuadraticSeventhPowerPacket.root_norm_eq
SevenQuadraticSeventhPowerPacket.root_norm_not_seven_dvd
```

The first derives
`norm p.root = (p.residual.powerSplit.b : ℤ)` from the existing residual norm
seventh power and `traceOne_norm_pow`, using nonnegativity of the discriminant
`-7` norm.  The second combines this equality with
`SevenAdicPowerSplit.seven_not_dvd_b`.

## 4. Mod-7 ramified coordinates

The new root-side consequence

```lean
SevenQuadraticSeventhPowerPacket.root_linear_mod_seven_ne_zero
```

shows that
`root.fst + 4 * root.snd` is nonzero in `ZMod 7`, because the norm is a
7-unit and the existing norm-square congruence applies.  Therefore

```lean
SevenQuadraticSeventhPowerPacket.ramified_coordinates_mod_seven_ne_zero
```

proves that both explicit ramified seventh-power coordinates are nonzero
modulo 7.  This is compatible with the ramified endpoint sector; it is not a
terminal contradiction.

## 5. Strongest checked root.snd depth

The module reuses
`ramifiedCoordinateNormalForm_of_packet` and the explicit identity

```text
2 * cyclotomicSevenFst z y + cyclotomicSevenSnd z y
  = (z-y) * (2*z^2 + 3*z*y + 2*y^2)
```

together with
`2 * ramifiedSeventhFst + ramifiedSeventhSnd = -7 * seventhPowerSnd`.
Since `z-y = 7^6*a^7`, and the quadratic factor is itself divisible by 7
when `7 ∣ z-y`, this yields

```lean
SevenQuadraticSeventhPowerPacket.seven_pow_five_dvd_root_snd
```

namely `7^5 ∣ p.root.snd`.  The final extraction uses
`seventhPowerSnd = 7 * root.snd * seventhPowerSndCore` and the checked
7-unit theorem for `seventhPowerSndCore`.  This is a lower-bound divisibility
result, not the historical exact valuation formula
`5 + 7 * padicValNat 7 gapRoot`.

## 6. Shallow consistency and obstruction result

The API audit checks the reduced root-side witness
`root = ⟨1, 7^5⟩` for:

```text
7 ∤ norm root
7^5 ∣ root.snd
7 ∤ seventhPowerSndCore root.fst root.snd
```

This is explicitly not a Fermat counterexample and not a witness to a
`SevenQuadraticSeventhPowerPacket`; it only rules out treating these reduced
root-side constraints as an automatic contradiction.

The full shallow packet constraint set therefore has no checked direct
contradiction in this checkpoint.  FLT7TC-001 materially shortened the proof
by supplying the explicit coordinate factorization and core-unit lemma used
above.  FLT7TC-002's generic parent provenance repair does not identify the
generic and specialized packets and does not add a new specialized invariant
here.

## 7. Old summit reachability and next bridge

The specialized packet contains the data needed to reach the field surface of
`PrimitiveRamifiedSummitPacket`: use

```text
endpointLeft := z, endpointRight := y, distinguished := x,
gapRoot := residual.powerSplit.a,
residualRoot := residual.powerSplit.b,
root := p.root.
```

The remaining fields are supplied by the existing counterexample positivity,
coprimality, endpoint nonzero, split, coordinate, and norm APIs.  However,
the new shallow module deliberately does not import
`SevenBaseTerminalRamifiedSummit.lean` or construct that deep structure.

The exact FLT7TC-004 bridge should be a small specialized-packet adapter that
imports the old summit definition only at the bridge boundary and fills the
above fields directly.  It must prove the cyclotomic residual equality from
the existing GN/norm identity and retain the current `root_norm_eq` result;
it must not route through historical Row-Y/Row-Z terminal profiles or claim a
contradiction from the summit type alone.

## 8. Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven.CoordinateNormalForm
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Seven.SeventhPowerCoordinates
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedObstructionApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedObstructionAxiomAudit
```

The new public theorem axiom audit reports only the inherited foundational
surface `[propext, Classical.choice, Quot.sound]`.  No project axiom,
`sorryAx`, `sorry`, `admit`, or `unsafe` proof was added.  A fresh-source
forbidden-construct scan and `git diff --check` completed without diagnostics.

## Outcome

**Outcome B — SHALLOW RAMIFIED DEPTH PACKAGE GREEN; NO DIRECT CONTRADICTION;
OLD SUMMIT BRIDGE IS THE NEXT HONEST FRONTIER**.
