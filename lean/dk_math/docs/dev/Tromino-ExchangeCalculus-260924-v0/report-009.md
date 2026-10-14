# TRM-010 report: recursive CosmicFormula scale bridge

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-010 gives an exact numerical calibration between the arbitrary-level
recursive Tromino mass split and the degree-two equal-axis CosmicFormula. The
calibration is componentwise; no equality of packet structures, recursive
cells, or geometric positions is asserted.

BoundaryIR, graph traversal, physical flattening, residual optimization, and
Four Color claims remain outside this checkpoint.

## Level side scale

`macroSideScale k` is defined by

```lean
macroSideScale k := 2 ^ (k + 1)
```

The kernel-checked scale identity is:

```text
macroSideScale k ^ 2 = 4 ^ (k + 1)
```

The regression values are `macroSideScale 0 = 2` and
`macroSideScale 1 = 4`.

## Recursive mass packet

`recursiveMassSplit k M : BodyGapSplit Nat` owns:

```text
big  = atomicMass (k+1) M
body = bodyAtomicMass k M
gap  = gapAtomicMass k M
```

Its split certificate is the existing recursive theorem
`body_gap_mass_split k M`, transported into the packet orientation.

## CosmicFormula packet

`recursiveCosmicSplit k : BodyGapSplit Nat` uses the existing degree-two
equal-scale quantities:

```text
big  = CoreBeamGap.Big 2 s(k) s(k)
body = CosmicFormulaBinom.BodyN 2 s(k) s(k)
gap  = CoreBeamGap.Gap 2 s(k)
```

where `s(k) = macroSideScale k`. Its split certificate is the existing
`CoreBeamGap.big_eq_body_add_gap` theorem. `GN` and `GTail` were not unfolded.

## Component formulas and calibration

The bridge proves:

```text
recursiveCosmicSplit k .gap  = 4^(k+1)
recursiveCosmicSplit k .body = 3*4^(k+1)
recursiveCosmicSplit k .big  = 4^(k+2)
```

For every `M : ScaledMacroCell (k+1)`,
`recursive_threeWay_cosmic_calibration` proves equality of the big, body, and
gap components of the recursive and CosmicFormula packets. Packet structure
equality is intentionally not used because it would compare proof fields.

The previous checkpoint calibrations are recovered exactly:

```text
k = 0: side = 2, gap = 4, body = 12, big = 16
k = 1: side = 4, gap = 16, body = 48, big = 64
```

## Core / Beam / Gap refinement

At the same equal scale, the numerical refinement is:

```text
Core = 4^(k+1)
Beam = 2*4^(k+1)
Gap  = 4^(k+1)
Big  = Core + Beam + Gap
```

This is only a mass/count statement. No one of the three Tromino body
positions is identified with Core, and no orientation or boundary convention
is introduced.

## Scaled unit law

The recursive law is also exposed relative to the gap unit:

```text
bodyAtomicMass k M = 3 * gapAtomicMass k M
atomicMass (k+1) M = 4 * gapAtomicMass k M
```

Thus the exact reading is `3G + G = 4G` with
`G = 4^(k+1)`.

## Computability and axiom audit

All new data definitions are computable. No declaration is marked
`noncomputable`; no new `axiom`, `sorry`, `admit`, or `unsafe` declaration was
added. The audited theorem dependencies contain only standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies inherited from
the existing certified finite and CosmicFormula infrastructure.

The bridge does not by itself suggest a boundary-signature invariant for the
next checkpoint: the new equalities are numerical conservation identities and
carry no positional or orientation data. Any boundary invariant requires a
separate reviewed API.

## Regression audit

`DkMathTest/Tromino/RecursiveCosmicBridgeAxiomAudit.lean` checks:

1. side scales `2` and `4`;
2. the general square/mass identity;
3. all fields of the recursive mass packet;
4. CosmicFormula values `16/12/4` at `k=0`;
5. CosmicFormula values `64/48/16` at `k=1`;
6. general componentwise recursive/CosmicFormula calibration;
7. Core, Beam, and Gap formulas;
8. `Big = Core + Beam + Gap`;
9. the two scaled-unit-law corollaries.

## Validation

Focused build:

```text
lake build DkMath.Tromino.RecursiveMacro \
  DkMath.Tromino.RecursiveCosmicBridge \
  DkMathTest.Tromino.RecursiveCosmicBridgeAxiomAudit
```

Result: successful (`Build completed successfully (8953 jobs)`).
`git diff --check` and the explicit untracked-file checks completed without
whitespace errors. The new production, audit, and report files were scanned for
forbidden constructs; no implementation occurrence was found.

## Stop boundary

TRM-010 stops at the exact arbitrary-level mass calibration with the degree-two
equal-scale CosmicFormula. Positional Core/Beam assignment, BoundaryIR, graph
traversal, physical flattening, residual optimization, and Four Color claims
remain deferred pending review.
