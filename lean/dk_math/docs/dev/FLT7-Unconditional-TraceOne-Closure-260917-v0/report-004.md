# FLT7TC-004 — Direct specialized-packet to primitive ramified summit bridge

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-004.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint adds only the direct bridge into the common ramified summit;
it does not replay the historical Row-Y/Row-Z route or claim a contradiction
from the summit's existence.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneRamifiedSummitBridge.lean`
- `DkMath/FLT/Seven.lean` (facade export)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneRamifiedSummitBridgeApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneRamifiedSummitBridgeAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

The attached `instruction-004.md` was preserved unchanged.

## 2. Direct adapter and field provenance

The new public definition has the signature:

```lean
SevenQuadraticSeventhPowerPacket.toPrimitiveRamifiedSummitPacket
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    PrimitiveRamifiedSummitPacket
```

It sets

```text
endpointLeft  := z
endpointRight := y
distinguished := x
gapRoot       := p.residual.powerSplit.a
residualRoot  := p.residual.powerSplit.b
root          := p.root
```

The remaining fields are sourced as follows:

- `gapRoot_pos`, `residualRoot_pos`, `gap_eq`, `residual_eq`,
  `distinguished_eq`, and `residualRoot_not_seven_dvd` come from
  `s := p.residual.powerSplit`.
- `endpoint_coprime` comes from
  `coprime_y_z_of_counterexamplePack s.sevenAdic.counterexample`, with the
  original `(y,z)` order transferred to `(z,y)`.
- endpoint nonzeroness and `endpointSum_ne_zero` come from the original
  positive counterexample.
- `coordinate_coprime` comes from
  `counterexample_cyclotomicSeven_coordinates_isCoprime` for the same source.
- `endpointRight_not_seven_dvd` is the existing
  `s.sevenAdic.seven_not_dvd_y` fact.
- `fermat_eq` is the signed integer form of the original `hEq`.
- `coordinate_eq` is copied from `p.coordinate_eq`.
- `root_norm_eq` is copied from the FLT7TC-003 theorem `p.root_norm_eq`.

For the remaining summit identity, the adapter proves

```text
cyclotomicSeven (z : ℤ) (y : ℤ) = 7 * (s.b : ℤ)^7
```

from the natural split `s.residual_eq`, the checked order `y ≤ z`, and
`GN_seven_sub_eq_traceOneNorm_negTwo` together with
`cyclotomicSeven_eq_traceOneNorm_negTwo`.  No six-degree polynomial is
re-expanded.

## 3. Witness preservation and exact depth

The root and both natural split witnesses are the same terms as in the input
packet.  The API audit checks the three equalities definitionally (`rfl`):

```text
summit.root       = p.root
summit.gapRoot    = p.residual.powerSplit.a
summit.residualRoot = p.residual.powerSplit.b
```

No fresh seventh-power witness or `Classical.choose` is introduced by the
adapter.

The exact historical depth formula is pulled back directly:

```lean
SevenQuadraticSeventhPowerPacket.rootSnd_padicValNat_exact
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    padicValNat 7 (Int.natAbs p.root.snd) =
      5 + 7 * padicValNat 7 p.residual.powerSplit.a
```

This is an application of
`PrimitiveRamifiedSummitPacket.rootSnd_padicValNat` to the adapter; the
historical valuation algebra is not duplicated.  Thus FLT7TC-003's

```text
7^5 ∣ p.root.snd
```

is a weaker consequence of the exact formula, not a separate contradiction.
The exact formula remains compatible with `7 ∤ norm p.root`.

## 4. Historical reachability audit

The source/API audit gives the following boundary.

### A. Pure-summit consumers

`SevenBaseTerminalRamifiedDepth.lean` consumes only
`PrimitiveRamifiedSummitPacket`.  It supplies the exact depth formula,
nonvanishing and 7-unit facts for the root second coordinate, and the related
ramified arithmetic.  The new adapter enters this layer directly.

### B. Summit plus cheaply derivable structure

The existing routing layer consumes a common summit and derives root-coordinate
coprimality, coordinate routing, and further ramified nondivisibility facts.
The gap-unit bridge constructs `RamifiedGapUnitBridgePacket` from a summit;
the unit-class and residual-root-class modules then expose their existing
modulo-7/modulo-49 consequences.  These are reusable from the adapter together
with the existing pure-summit constructors; none requires replaying the old
terminal row selection.

### C. Provenance-sensitive consumers

The first unavailable exact input is
`TerminalPrimitiveRamifiedSummitPacket`, whose additional data are

```text
carrierUnit > 0,
7 ∤ carrierUnit,
carrierUnit = summit.gapRoot * summit.residualRoot,
Nat.Coprime summit.gapRoot summit.residualRoot.
```

This packet retains the selected terminal carrier that the common summit
deliberately forgets.  Existing constructors obtain it from
`AwaySevenBaseTerminalRowYProfile`, `AwaySevenBaseTerminalRowZProfile`, or a
terminal unit-sector packet.  Those are historical terminal/away provenance,
not data supplied by the direct specialized packet.  Consequently the new
adapter must not manufacture this stronger packet.

### D. Heavy fusion/reconstruction frontier

Canonical split, inner-root extraction, and the later degree-six/fusion
modules require the terminal packet or still stronger routing objects.  The
named U1.6 boundary is
`InternalDepthFourCounterexampleReconstructionObligation`: an actual
`AwayValuationTransferPacket` whose carrier is the extracted internal depth-four
coordinate.  This checkpoint constructs no inhabitant of that proposition and
does not introduce recursive descent.

The deepest honest reusable endpoint reached here is therefore the common
`PrimitiveRamifiedSummitPacket`, together with the pure-summit-derived
ramified depth/routing/gap-unit and residual-root congruence APIs.  The first
missing downstream input is the provenance-sensitive
`TerminalPrimitiveRamifiedSummitPacket`, not the exact valuation formula.

## 5. Architectural conclusion and outcome

The adapter bypasses the historical route used to construct the common summit
from selected Row-Y/Row-Z terminal data.  It does not bypass a genuinely new
provider for the terminal carrier: the specialized packet already contains the
original counterexample, split witnesses, and root, so the bridge packages data
that were available from that actual ramified counterexample.  It shortens the
entry path into the historical pure-summit arithmetic, but it does not solve
the U1.6 reconstruction obligation and does not produce a contradiction.

**Outcome B — SUMMIT BRIDGE GREEN; HISTORICAL PURE-SUMMIT ROUTE REACHES A NEW
PRECISE FRONTIER BUT NO CONTRADICTION**.

The next focused ramified frontier is explicit: justify or refute a genuine
terminal-carrier/provenance bridge from the specialized packet before claiming
access to `TerminalPrimitiveRamifiedSummitPacket`.  No such bridge is claimed
here.  The away branch remains the next named roadmap checkpoint after this
frontier is recorded.

## 6. Validation

The required focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction
lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit
lake build DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth
lake build DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedSummitBridgeApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneRamifiedSummitBridgeAxiomAudit
```

The bridge axiom audit reports only the inherited foundational surface
`[propext, Classical.choice, Quot.sound]` for both public declarations.  The
new production and API-audit sources contain no `sorry`, `sorryAx`, `admit`,
`axiom`, or `unsafe` declaration.  `git diff --check` and the new-file
whitespace check completed without diagnostics.
