# instruction-002 — isolate the dormant heavy theta-jet existence branch

## Goal

Phase 1 established `PrimeAdicPowerSplit`. Before the next FLT7-to-prime generalization audit, reduce the cost of the ordinary `DkMath.FLT.Seven` facade build without deleting any proved mathematics.

The target is the currently expensive side chain

```text
SevenRealCubicSourcePlane
  -> SevenRealCubicThetaCoordinates
  -> SevenRealCubicThetaSeventhPower
  -> SevenRamifiedThetaJetLifting
  -> SevenRamifiedPairedThetaRootJet
```

The expensive declarations in `SevenRealCubicThetaSeventhPower` and `SevenRamifiedThetaJetLifting` are used to construct existence of a paired theta-root-jet packet, but the later FUSION chain consumes `RamifiedPairedThetaRootJetPacket` and its structural consequences as an input type. The public theorem

```lean
RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet
```

is not used by the FLT7 production proof chain beyond axiom-audit coverage.

Do **not** remove the packet type or its structural theorems. Isolate only the heavy existence constructor path.

## Verified dependency observation

Before editing, re-run repository search and record the exact consumers of:

```text
RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet
nonempty_triangularThetaJetExact
SevenRealCubicInt.thetaLinear_pow_seven
SevenRealCubicInt.thetaSquare_pow_seven
RamifiedPairedThetaRootJetPacket
```

Expected shape:

- `nonempty_pairedThetaRootJet` is consumed only by its declaration site and `DkMathTest.FLT.Seven.CheckAxioms`.
- `nonempty_triangularThetaJetExact` is consumed by the private paired-root constructor plus axiom audit.
- `thetaLinear_pow_seven` / `thetaSquare_pow_seven` are consumed by the paired-root existence construction / theta-jet lifting plus axiom audit.
- `RamifiedPairedThetaRootJetPacket` itself is consumed widely by `SevenRamifiedFusion*`; therefore its defining module is **not** a dead module.

If repository search contradicts this, stop the import surgery and report the additional production consumer.

## Part A — split structural packet from existence construction

Refactor

```text
DkMath/FLT/Seven/SevenRamifiedPairedThetaRootJet.lean
```

so that it no longer imports

```lean
import DkMath.FLT.Seven.SevenRamifiedThetaJetLifting
```

and no longer contains the heavy existence proofs.

Keep in this structural module:

- `RamifiedThetaRootJetPacket`
- `RamifiedPairedThetaRootJetPacket`
- all theorems/defs that take an existing `RamifiedPairedThetaRootJetPacket` as input
- `linearCore_gap_modSeven`
- `squareCore_gap_modSeven`
- `gapCore_thetaResidue_eq`
- `left_not_sourcePlane`
- `right_not_sourcePlane`
- `fusionSlope` and its consequences
- unit-grid / sector address structure already present in this file

Use the minimum direct imports needed for these declarations. It is acceptable and preferable to import `SevenRealCubicThetaCoordinates`, `SevenRamifiedSignedRootDepth`, and/or `SevenRamifiedFusionUnitSector` explicitly rather than relying on the heavy lifting module as a transitive import.

Move the following construction-only declarations into a new file:

```text
DkMath/FLT/Seven/SevenRamifiedPairedThetaRootJetExistence.lean
```

The new file should import:

```lean
import DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet
import DkMath.FLT.Seven.SevenRamifiedThetaJetLifting
```

Move/reconstruct there:

- the private `nonempty_thetaRootJet`
- `RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet`

Preserve the theorem name, namespace, statement, and proof semantics of `nonempty_pairedThetaRootJet`. This is a module-boundary refactor, not a mathematical rewrite.

Do not duplicate the packet structures between modules.

## Part B — remove the heavy branch from the ordinary FLT7 facade

Edit

```text
DkMath/FLT/Seven.lean
```

so the ordinary facade does **not** directly import:

```text
SevenRealCubicThetaSeventhPower
SevenRamifiedThetaJetLifting
SevenRamifiedPairedThetaRootJetExistence
```

It must continue to import the structural:

```text
SevenRamifiedPairedThetaRootJet
```

because downstream FUSION modules use `RamifiedPairedThetaRootJetPacket` and its structural API.

Do not broadly prune unrelated imports in this instruction. In particular, do not remove `SevenRealCubicSourcePlane` or `SevenRealCubicThetaCoordinates` merely because they occur earlier in the expensive historical chain; they have lightweight structural users elsewhere. The objective is to remove the two known high-cost proof modules from the default dependency closure.

Add a short facade comment explaining that the proved theta-jet existence branch is intentionally available through `SevenRamifiedPairedThetaRootJetExistence` but omitted from the ordinary facade because no current production endpoint consumes the existence theorem.

## Part C — split axiom audit coverage

`DkMathTest/FLT/Seven/CheckAxioms.lean` currently imports `DkMath.FLT.Seven`, so after Part B it must no longer print declarations that are available only through the dormant heavy branch.

Move the heavy-branch `#print axioms` checks into a new test module, for example:

```text
DkMathTest/FLT/Seven/CheckAxiomsThetaJetExistence.lean
```

which imports:

```lean
import DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJetExistence
```

Move at least these checks there:

```text
RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet
triangularJet_depth_step
triangularJet_depth_three_six
nonempty_triangularThetaJetExact
triangularJetJacobianDet_ne_zero
SevenRealCubicInt.thetaLinear_pow_seven
SevenRealCubicInt.thetaSquare_pow_seven
```

If additional declarations in the current axiom test cease to resolve after removing the heavy facade import, classify them by actual dependency. Move only declarations genuinely belonging to this heavy theta-jet existence branch.

The ordinary `CheckAxioms` must retain all checks for downstream FUSION structural theorems that remain exported by `DkMath.FLT.Seven`.

## Part D — verification

Required focused builds:

```bash
lake build DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet
lake build DkMath.FLT.Seven.SevenRamifiedFusionSectorEquiv
lake build DkMath.FLT.Seven.SevenRamifiedFusionRoutingAudit
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.Seven.CheckAxioms
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility
```

The key success criterion is that the ordinary

```bash
lake build DkMath.FLT.Seven
```

no longer has `SevenRealCubicThetaSeventhPower` or `SevenRamifiedThetaJetLifting` in its source import closure.

Verify this from the source import graph, not merely from cached build output.

Then separately verify the dormant branch:

```bash
lake build DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJetExistence
lake build DkMathTest.FLT.Seven.CheckAxiomsThetaJetExistence
```

These two commands are allowed to remain slow. They certify that the mathematics was retained even though it is no longer in the ordinary FLT7 facade.

No new `sorry`, `axiom`, or `sorryAx` dependency is permitted.

## Part E — report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-002.md
```

Report:

1. exact pre-refactor consumers of the heavy declarations;
2. exact declarations moved to the existence module;
3. imports removed/added;
4. whether downstream FUSION structural modules compile without the heavy chain;
5. whether `lake build DkMath.FLT.Seven` now excludes the two expensive modules from its import closure;
6. separate dormant-branch build result;
7. axiom audit result;
8. any API surface lost from importing `DkMath.FLT.Seven` alone.

## Non-goals

Do not in this instruction:

- delete `SevenRealCubicThetaSeventhPower.lean`;
- delete `SevenRamifiedThetaJetLifting.lean`;
- alter the mathematical statements of their theorems;
- generalize the theta-jet machinery from `7` to arbitrary `p`;
- rewrite downstream `SevenRamifiedFusion*` mathematics;
- modify `PrimeAdicPowerSplit` except to fix an import regression caused by this refactor;
- claim an FLT7 or general FLT contradiction.

## Decision after report-002

If the ordinary FLT7 facade builds without the heavy existence branch and downstream FUSION modules remain green, treat this as an architectural cleanup only. Then resume the prime-generalization audit at the next seven-specific frontier downstream of `PrimeAdicPowerSplit`.
