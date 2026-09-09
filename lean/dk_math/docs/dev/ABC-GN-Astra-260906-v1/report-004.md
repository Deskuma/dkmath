# LUNA-004 — Mordell-coordinate production bridge

This checkpoint adds only the exact algebraic transport from the production
square-cube/Pell coordinates to a Mordell equation. It does not formalize any
point count, rank estimate, external theorem, or asymptotic bound.

## 1. Files changed

Added [GNExcessCubicMordellTransport.lean](../../../DkMath/ABC/GNExcessCubicMordellTransport.lean)
and imported it from `DkMath/ABC.lean` immediately after
`GNExcessCubicShellParameterBounds`. Added the focused and aggregator logs
[lean-004-output.txt](lean-004-output.txt),
[build-004-abc-output.txt](build-004-abc-output.txt), and this report plus
[validation-004.txt](validation-004.txt).

The module imports only `DkMath.ABC.GNExcessCubicShellParameterBounds`.

## 2. Generic integer identity

`cubicPell_to_Mordell_identity` proves over `ℤ` that

```text
y² + 3 = 4*S*r³*u²
  → (4*S*u²*y)² = (4*S*u²*r)³ - 48*S²*u⁴.
```

The proof is a polynomial calculation: multiply the input equation by
`16*S²*u⁴`, then normalize with `ring`. The theorem does not mention or
depend on integral-point counting.

## 3. Nat identity status

`cubicPell_to_Mordell_identity_nat` exposes the subtraction-free form

```text
(4*S*u²*y)² + 48*S²*u⁴ = (4*S*u²*r)³.
```

This is the convenient public form for production natural coordinates. The
integer subtraction form remains available for later coordinate consumers.

## 4. Production square-cube conic wrapper

`GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic` takes a shell
witness `a` and proves directly

```text
(2*a+3)² + 3 = 4*S*r³*u²,
```

where

```text
M = GNExcessCubicFullRepeatedModulus a
r = oddPart M
u = GNExcessCubicSquarefulQuotient M
S = GNExcessCubicComplement a.
```

The proof composes the existing complement packet, the existing squareful
identity `M=u²*r³`, and the discriminant identity for `a²+3a+3`. No
existential coordinate choice is introduced.

## 5. Production Mordell identity

`GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity` applies the
Nat bridge to every production shell witness. It proves the exact
subtraction-free equation with the canonical expressions:

```text
(4*S*u²*(2*a+3))² + 48*S²*u⁴ = (4*S*u²*r)³.
```

Equivalently, over integers this is the Mordell equation with coefficient
`-48*S²*u⁴`. No elliptic-curve structure is defined.

## 6. Fixed-`(S,u)` injectivity

`mordellCoordinates_injective_fixed_SU` proves that for positive fixed `S,u`,

```text
4*S*u²*r₁ = 4*S*u²*r₂
4*S*u²*(2*a₁+3) = 4*S*u²*(2*a₂+3)
```

implies `r₁=r₂` and `a₁=a₂`. The proof is positive natural cancellation
followed by `omega` for the affine coordinate. It does not claim injectivity
when `S` or `u` varies.

## 7. Optional image status

Skipped. The main bridge and the fixed-coefficient injectivity theorem are
available without creating another finite image or fiber hierarchy. Future
research can define such an image at the point where a concrete consumer
needs it.

## 8. Explicit no-counting boundary

PROVED:

- every production shell witness gives an exact equation
  `Y² = Z³ - 48*S²*u⁴` in the equivalent integer form;
- the canonical production conic is exactly `y²+3=4*S*r³*u²`;
- for positive fixed `(S,u)`, the coordinate map `(a,r) ↦ (Z,Y)` is injective.

NOT PROVED:

- every integral Mordell point is a production witness;
- a uniform integral-point count;
- the Helfgott–Venkatesh specialization in Lean;
- a rank bound;
- the `31/24+ε` moment bound;
- a balanced-box power saving;
- ABC.

The scratch Eisenstein coordinate identities were intentionally not ported.

## 9. Focused build

The required command passed:

```text
lake build DkMath.ABC.GNExcessCubicMordellTransport
```

The output is retained in [lean-004-output.txt](lean-004-output.txt).

## 10. ABC aggregator build

The required command passed:

```text
lake build DkMath.ABC
```

The output is retained in [build-004-abc-output.txt](build-004-abc-output.txt).
The new import is immediately after `GNExcessCubicShellParameterBounds`;
unrelated imports were not reordered.

## 11. Forbidden scan

The new production module was scanned for:

```text
sorry, admit, axiom, abc_main_axiom, native_decide, unsafe
```

No occurrences were found. No external theorem enters the dependency graph.

## 12. Axiom audit

The focused build reports:

```text
cubicPell_to_Mordell_identity: [propext]
cubicPell_to_Mordell_identity_nat: [propext]
GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic:
  [propext, Classical.choice, Quot.sound]
GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity:
  [propext, Classical.choice, Quot.sound]
mordellCoordinates_injective_fixed_SU:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs in the new declarations.

## 13. Remaining research frontier

The production graph now contains an exact algebraic bridge from a shell
witness to the fixed-field-shaped Mordell family used in the research report.
It still contains no theorem about how many integral points that family has,
how those points average over `(S,u)`, or how to obtain balanced-box sparsity.

This completes LUNA-004 at its requested stop condition. No LUNA-005
instruction is opened automatically.
