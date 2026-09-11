# FLT prime-generalization Phase 2 — dormant theta-jet existence branch

## Scope

This report implements the bounded module-boundary refactor in
`instruction-002.md`.  The proved theta-jet existence mathematics is retained,
while the ordinary `DkMath.FLT.Seven` facade no longer closes over its two
expensive proof modules.  No theorem statement or downstream FUSION
mathematics was changed.  This is an architectural cleanup; it is not an FLT7
or general FLT contradiction.

## Part A — verified pre-refactor consumers

Before editing, repository search was run for the five declarations named by
the instruction.

- `RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet` occurred at its
  declaration in `SevenRamifiedPairedThetaRootJet.lean` and in
  `DkMathTest.FLT.Seven.CheckAxioms`.
- `nonempty_triangularThetaJetExact` occurred in the private paired-root
  constructor, at its declaration in `SevenRamifiedThetaJetLifting.lean`, and
  in the axiom audit.
- `SevenRealCubicInt.thetaLinear_pow_seven` and
  `SevenRealCubicInt.thetaSquare_pow_seven` occurred in the paired-root
  existence construction / theta-jet lifting branch and in the axiom audit.
- `RamifiedPairedThetaRootJetPacket` had many production consumers in
  `SevenRamifiedFusion*`, including the sector-equivalence, routing-audit,
  cyclic-bridge, and real-pair-carrier modules.  Its defining structural
  module was therefore retained.

The search found no additional production consumer of the existence theorem
or the construction-only theta declarations.  The packet type and structural
consequences were not classified as dormant.

## Part B — structural/existence split

`SevenRamifiedPairedThetaRootJet.lean` now contains only the packet structures
and their structural/unit-grid/FUSION-facing consequences.  Its direct imports
are `SevenRamifiedSignedRootDepth` and `SevenRamifiedFusionUnitSector`; it no
longer imports `SevenRamifiedThetaJetLifting`.

The new
`SevenRamifiedPairedThetaRootJetExistence.lean` imports the structural packet
module and `SevenRamifiedThetaJetLifting`.  It contains the moved/reconstructed
construction-only declarations:

- the private `nonempty_thetaRootJet` theorem;
- `RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet`.

The public theorem name, namespace, statement, and proof semantics are
preserved, and the packet structures are not duplicated.

## Part C — ordinary facade and axiom audits

`DkMath.FLT.Seven` keeps `SevenRealCubicSourcePlane`,
`SevenRealCubicThetaCoordinates`, and the structural
`SevenRamifiedPairedThetaRootJet` import.  It no longer directly imports
`SevenRealCubicThetaSeventhPower`, `SevenRamifiedThetaJetLifting`, or the new
existence module.  A facade comment records that the proved existence branch
remains available through the explicit existence module.

The ordinary `CheckAxioms.lean` retains the exported structural and FUSION
checks.  The seven heavy-branch checks were moved to
`CheckAxiomsThetaJetExistence.lean`, which imports
`SevenRamifiedPairedThetaRootJetExistence`.

The source import graph was checked directly.  The only path to the two heavy
modules is now the explicit existence branch:

```text
SevenRamifiedPairedThetaRootJetExistence
  -> SevenRamifiedThetaJetLifting
  -> SevenRealCubicThetaSeventhPower
```

No direct heavy-module import remains in `DkMath/FLT/Seven.lean` or the
structural packet module.

## Verification

The required focused builds passed:

```text
lake build DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet
lake build DkMath.FLT.Seven.SevenRamifiedFusionSectorEquiv
lake build DkMath.FLT.Seven.SevenRamifiedFusionRoutingAudit
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.Seven.CheckAxioms
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility
```

The ordinary facade build completed successfully in 8808 jobs.  Its source
import closure excludes both `SevenRealCubicThetaSeventhPower` and
`SevenRamifiedThetaJetLifting`.  The downstream FUSION sector-equivalence and
routing-audit builds also completed successfully without importing the heavy
existence chain.

The retained dormant branch was built separately:

```text
lake build DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJetExistence
lake build DkMathTest.FLT.Seven.CheckAxiomsThetaJetExistence
```

Both completed successfully.  The existence module build completed in 8767
jobs, and its dedicated axiom test completed in 8768 jobs.

The ordinary axiom test completed successfully in 8809 jobs.  The dedicated
heavy-branch audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the checked declarations.  The ordinary audit likewise has
no `sorryAx`.  Source scans of the changed facade, structural module,
existence module, and both axiom-test files found no `sorry` or `axiom`
construct.

## API boundary

Importing `DkMath.FLT.Seven` alone no longer exposes the dormant existence
constructor and the heavy theta-jet declarations checked only by the separate
audit.  It still exposes `RamifiedPairedThetaRootJetPacket`, its structural
theorems, unit-grid/sector data, and the downstream FUSION API.  Clients that
need the retained existence theorem or its heavy prerequisites should import
`DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJetExistence` explicitly.

No FLT7 contradiction, general FLT theorem, or arbitrary-prime theta-jet
generalization is claimed.
