# LUNA-008 — Lib promotion and p=3 Eisenstein API reconciliation

## 1. Branch sync baseline

The checkout is `wip/ABC-GN-astra-260906-v1` and was clean before the LUNA-008 edits. The supplied reconciliation records that this branch had already been fast-forwarded to the current `develop` architecture. Source inspection confirmed that the newer `DkMath.Lib.NumberTheory` APIs (`PrincipalIdealPower`, `UnitPowerSector`, and related modules) are present. No commit hash is recorded here.

## 2. Files changed

Production changes:

- `DkMath/Lib/NumberTheory/EisensteinCoordinates.lean` (new canonical implementation).
- `DkMath/NumberTheory/EisensteinCoordinates.lean` (historical export facade).
- `DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean`.
- `DkMath/ABC/GNExcessCubicEisensteinFactorConsequences.lean`.
- `DkMath/Lib.lean`.
- `DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean`.
- `DkMath/FLT/Three/EisensteinLibBridge.lean` (new bridge).
- `DkMath/FLT/Three.lean`.

Validation outputs and the forbidden/warning scans are recorded beside this report.

## 3. Lib promotion

The reusable neutral coordinate core now lives in `DkMath.Lib.NumberTheory` in `DkMath/Lib/NumberTheory/EisensteinCoordinates.lean`. It imports only `DkMath.NumberTheory.TraceOneQuadratic`, retains the carrier `TraceOneInt (-1)`, and reuses the existing trace-one norm and ring. The complete coordinate, multiplication, norm, coprimality, and conditional cubic-coordinate consequence API was moved without changing theorem content.

## 4. Historical compatibility facade

`DkMath/NumberTheory/EisensteinCoordinates.lean` now imports the Lib module and exports the historical declarations under `DkMath.NumberTheory.EisensteinCoordinates`. It contains no duplicated proofs, so existing importers retain their names while the implementation has one owner.

## 5. ABC import migration

`GNExcessCubicEisensteinCoordinates.lean` now imports the Lib owner and opens `DkMath.Lib.NumberTheory`. `GNExcessCubicEisensteinFactorConsequences.lean` likewise opens the Lib namespace. The ABC theorem statements and conditional meaning are unchanged.

## 6. `DkMath.Lib` entry-point update

`DkMath/Lib.lean` imports `DkMath.Lib.NumberTheory.EisensteinCoordinates` with the other number-theory imports. The dependency direction is therefore `TraceOneQuadratic -> Lib.NumberTheory -> ABC/FLT bridges`; Lib does not depend on FLT.

## 7. `signedPrimeParameter_three`

`DkMath.NumberTheory.PrimeQuadraticDiscriminant` now proves

```lean
signedPrimeParameter 3 = -1
```

by direct normalization of `signedPrimeDiscriminant` and `signedPrimeParameter`.

## 8. Carrier identity status

The bridge theorem `traceOneInt_signedPrimeParameter_three_type` rewrites `signedPrimeParameter_three` to identify `TraceOneInt (signedPrimeParameter 3)` with `TraceOneInt (-1)`. The existing FLT3 abbreviation `EisensteinInt` is already `TraceOneInt (-1)`, so this is an API boundary closure rather than a new type equivalence.

## 9. Omega/tau coordinate bridge

`lib_eisensteinCoord_eq_FLT3_coord` records

```lean
Lib.eisensteinCoord m n = FLT.Three.eisensteinCoord m (-n)
```

by definitional equality. The essentially free companion theorem `lib_eisensteinCoord_norm_eq_FLT3_coord_norm` records norm compatibility. This is the sign change `tau = -omega` and introduces no second ring.

## 10. FLT3 cube-sector `UnitPowerSectorSystem`

`eisensteinCubeUnitPowerSectorSystem` packages the existing `EisensteinUnitSector` representatives (`1`, `tau`, and `tau^2`) as

```lean
UnitPowerSectorSystem (TraceOneInt (-1)) 3
```

Its completeness field consumes only `exists_sector_mul_cube_of_unit`; the returned `IsUnit delta` is converted with `.unit`. No new unit classification is proved.

## 11. Generic completeness theorem

`eisensteinCubeUnitPowerSectorSystem_complete` exposes the generic existential statement for every unit by applying the system's `.complete` field. It is an API wrapper over the existing FLT3 result.

## 12. Exact meaning of the former p=3 API boundary

The carrier mismatch is closed: both sides use `TraceOneInt (-1)`. The coordinate convention mismatch is closed by the explicit omega/tau sign bridge. The unit-sector packaging mismatch is closed by the `UnitPowerSectorSystem` wrapper. Full generic odd-prime p=3 facade integration is not claimed; the cyclotomic packets, stripped ideals, Dedekind/class-group hypotheses, and branch-specific interfaces remain outside this checkpoint.

## 13. Relation to new PrincipalIdealPower / UnitPowerSector APIs

The promoted Lib layer is structurally adjacent to `PrincipalIdealPower`, `PowerFactor`, `IdealPowerFactor`, and `UnitPowerSector`. Those APIs can serve as downstream machinery when a future proof supplies the required ideal-power and principalization hypotheses. LUNA-008 only packages the already-proved p=3 unit sectors.

## 14. Explicit no-ABC-factorization boundary

No theorem asserting `(a+2)+omega = beta * gamma^2` was added. No ABC factorization existence, uniqueness, counting, class-group theorem, asymptotic estimate, or Mordell bound was inferred from the Lib APIs. ABC remains unproved.

## 15. Focused builds

The following required targets completed successfully:

- `lake build DkMath.Lib.NumberTheory.EisensteinCoordinates` — `lean-008-eisenstein-lib-output.txt`.
- `lake build DkMath.NumberTheory.EisensteinCoordinates` — `lean-008-eisenstein-facade-output.txt`.
- `lake build DkMath.ABC.GNExcessCubicEisensteinFactorConsequences` — `lean-008-abc-factor-output.txt`.
- `lake build DkMath.FLT.Three.EisensteinLibBridge` — `lean-008-eisenstein-bridge-output.txt`.

## 16. Aggregator builds

The updated aggregators also completed successfully:

- `lake build DkMath.Lib` — `lean-008-lib-output.txt`.
- `lake build DkMath.ABC` — `lean-008-abc-output.txt`.
- `lake build DkMath.FLT.Three` — `lean-008-flt3-output.txt`.

## 17. Forbidden scan

Changed production Lean sources were scanned for `sorry`, `admit`, `axiom`, `abc_main_axiom`, `native_decide`, and `unsafe`. The scan produced zero matches; the empty result is recorded in `forbidden-scan-008.txt`. The filtered build-warning scan also produced zero new warnings in the recorded outputs (`warnings-scan-008.txt`).

## 18. Axiom audit

The promoted coordinate declarations and the bridge declarations were audited with `#print axioms`. The reported trust boundary is the expected subset of `propext`, `Classical.choice`, and `Quot.sound`; the coordinate equality bridge itself reports no axioms. The completeness theorem reports `propext`, `Classical.choice`, and `Quot.sound`, inherited from the existing unit and quotient infrastructure.

## 19. Remaining research frontier

The reconciliation stops at the requested API boundary. The ABC-GN research frontier remains actual Eisenstein factorization existence/counting for shell witnesses and/or balanced-box represented-pair sparsity. No LUNA-009 work or new counting research was started.
