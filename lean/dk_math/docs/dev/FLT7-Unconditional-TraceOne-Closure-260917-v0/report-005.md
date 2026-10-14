# FLT7TC-005 — Away-branch closure audit and reconstruction frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-005.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint compares the generic p = 7 away front door with the existing
specialized FLT7 away tower.  It does not identify independently chosen
existential witnesses, construct a new counterexample, or promote the existing
valuation drop to a recursive descent.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneAwayClosureAudit.lean`
- `DkMath/FLT/Seven.lean` (facade export)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneAwayClosureAuditApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneAwayClosureAuditAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

The attached `instruction-005.md` was preserved unchanged.

## 2. Generic p = 7 theorem surface

The new adapter is:

```lean
theorem CounterexamplePack.toPrimitivePrimeCounterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    DkMath.FLT.Prime.PrimitivePrimeCounterexample 7 x y z
```

It copies `hPack.hx`, `hPack.hy`, `hPack.hz`, `hPack.hxy`, and the original
Fermat equation, while supplying only the fixed facts `Nat.Prime 7` and
`3 ≤ 7`.  The endpoint triple remains exactly `(x,y,z)`.

The generic away theorem consumed through this adapter is:

```lean
DkMath.FLT.Prime.away_branch_power_factor_split
  hPack.toPrimitivePrimeCounterexample hgap
```

Its factor is `GTail 7 1 (z-y) y`; its underlying inputs also include the
generic `gap_mul_GTail_eq` and the generic away coprimality theorem.

## 3. Specialized p = 7 comparison

The specialized theorem surface is:

```lean
branchAway_seventh_power_factor_split hPack hgap
```

which uses `body7_eq_seventh_power_of_counterexample` and
`branchAway_coprime_gap_GN_seven`, and returns the same gap factor together
with `GN 7 (z-y) y` as a seventh power.

The new theorem
`counterexamplePack_away_split_gtail_iff_gn` proves the proposition-level
normalization

```text
GTail 7 1 (z-y) y = GN 7 (z-y) y
```

definitionally.  The theorem
`CounterexamplePack.away_branch_power_factor_split_iff_specialized` additionally
compares the generic and specialized theorem surfaces under the same `hPack`
and `hgap`.  This compares propositions only; it does not assert equality of
the `a` or `b` terms selected by separate existential proofs.

`AwayCoordinateNormalForm.away_factor_split_gtail` records that an existing
specialized away normal form already implies the normalized natural split.
The normal form retains strictly richer element-level data, including:

```text
counterexample
seven_not_dvd_gap
coordinate_eq
fst_eq / snd_eq
```

and the existing downstream API supplies `root_norm_not_seven_dvd`,
`root_coordinates_isCoprime`, the exact `AwayValuationTransferPacket.valuation_eq`,
and `root_snd_depth_lt_carrier`.  Thus the generic split contributes no
invariant absent from the specialized route; in particular it does not improve
the element-level coordinate/root equations.

## 4. Closure questions

For an existing away packet `p : AwayValuationTransferPacket x y z`:

1. The generic split supplies no new `nextX`, `nextY`, or `nextZ`; it only
   supplies existential seventh-power factors for the original gap and tail.
2. It supplies no new Fermat equation for a candidate triple.
3. It supplies no `CounterexamplePack nextX nextY nextZ` or primitive/coprime
   hypotheses for a candidate triple.
4. It does not identify a next route carrier with
   `Int.natAbs p.normal.root.snd`.
5. It supplies no away condition for a new packet, because no new packet is
   constructed.

The exact existing closure requirement remains:

```lean
structure AwayDescentClosureProvider
    (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd
```

No `AwayDescentClosureProvider` was constructed.  The exact missing data are
therefore a new primitive positive FLT7 counterexample, its away valuation
packet, and the displayed carrier match.  The already checked theorem
`AwayValuationTransferPacket.root_snd_depth_lt_carrier` proves the strict
valuation inequality once such a provider exists; it is not itself the
reconstruction.

## 5. Closure and ramified transition result

No direct arithmetic contradiction was found.  The simultaneous natural
seventh powers are consistent with the current checked data and are not used
as a contradiction.

No honest transition into the FLT7TC-004 ramified summit was built.  The
current away hypothesis is `¬ 7 ∣ z-y`, whereas the ramified summit bridge
requires the separate ramified packet and does not manufacture a new
counterexample from a smaller factor or a valuation resemblance.

The generic route therefore does not close or materially shrink the historical
reconstruction frontier.  The named `MissingClosureProviderStatement` and
`AwayClosureAuditResult.open` boundary remains the correct checked endpoint.

## Outcome

**Outcome B — GENERIC P=7 AWAY SPLIT NORMALIZES TO EXISTING SPECIALIZED DATA;
RECONSTRUCTION FRONTIER UNCHANGED**.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMath.FLT.Seven.CounterexampleRouting
lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
lake build DkMath.FLT.Seven.CoordinateNormalForm
lake build DkMath.FLT.Seven.AwaySecondCoordinateLoad
lake build DkMath.FLT.Seven.AwayValuationTransfer
lake build DkMath.FLT.Seven.DescentClosureAudit
lake build DkMath.FLT.Seven.PrimeTraceOneAwayClosureAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneAwayClosureAuditApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneAwayClosureAuditAxiomAudit
lake build DkMath.FLT.Seven
```

The new public declarations' axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.  Fresh production and API-audit
Lean sources contain no `sorry`, `sorryAx`, `admit`, `axiom`, or `unsafe`
declaration; the separate axiom-audit file contains only intentional
`#print axioms` commands.  `git diff --check` and the new-report whitespace
check completed without diagnostics.
