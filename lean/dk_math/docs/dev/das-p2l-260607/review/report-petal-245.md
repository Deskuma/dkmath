# Report: petal-245

## Branch

Added mnemonic names for the unfilled Gap regions and future proof opcodes.

This checkpoint intentionally assigns names first.  It does not yet assign
proofs to every opcode slot.

## Updated File

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
```

## Added Gap Names

```lean
inductive SourcePressureGapName where
  | missingFailureInput
  | unresolvedResolutionBranch
  | missingBeamSeed
  | missingPulseBox
  | missingNeighborCandidate
  | missingOrientation
  | missingAdjacentDiagnosis
  | unresolvedOverlapObstruction
  | missingTransport
  | missingCanonicalSelection
  | missingCoverage
  | missingAggregation
```

These are names only.

They mean:

```text
this transition has no assigned proof opcode yet
```

They do not mean contradiction, impossibility, or failure of the mathematics.

## Added Opcode Names

```lean
inductive SourcePressureOpcodeName where
  | enterFailureResolution
  | splitResolution
  | enterBeamSeed
  | extractPulseBox
  | projectNeighborMembership
  | projectNeighborDiagnostic
  | attachForwardOrientation
  | attachReverseOrientation
  | attachAdjacentDiagnosis
  | closeAsOverlapObstruction
  | markNoTransport
  | markNoCoverage
  | markNoCanonicalSelection
```

These names describe proof-producing moves or formally recorded blockage
markers.  They are not executable automaton instructions yet.

## Table Shape

The intended future table is now explicit in source comments:

```text
state bits + gap name -- assigned opcode --> next named state
```

First unfilled cells:

```text
NeighborCandidate alone
  -> missingOrientation
  -> missingAdjacentDiagnosis

CenteredPulseBox alone
  -> missingBeamSeed

OrientedNeighborDiagnostic
  -> missingTransport
  -> missingCoverage
```

## Why This Is Useful

This gives stable labels for the regions that are not yet filled.  Future
agents can attach one of three things to each Gap name:

- a positive bridge theorem;
- a formal impossibility/negative theorem;
- an obstruction witness.

That matches the project strategy: name the unknown region first, then assign
proof opcodes as the surrounding theorem network becomes strong enough.

## Verification

Commands run from:

```text
lean/dk_math
```

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

No-sorry check:

```text
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
```

Result: no matches.

Whitespace check:

```text
git diff --check
```

Result: passed.
