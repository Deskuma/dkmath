# GNIP-002 report — Collatz gnomon compatibility recovery

## 1. Outcome

**A — COMPATIBILITY RECOVERY COMPLETE.**

The application-independent square-gnomon layer in
`DkMath.Collatz.GnomonEvaluation` now reuses `DkMath.Gnomon.Algebra`, while
the existing Collatz public names and Collatz-specific dynamics remain in
place.

## 2. Changed files

```text
DkMath/Collatz/GnomonEvaluation.lean
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-002.md
```

The only production source change is the neutral import and the compatibility
refactor in `GnomonEvaluation.lean`.  No Legendre, MultiGauge, GTail/Cosmic,
Pascal, Polyomino, FLT, or ABC module was changed.

## 3. Neutral source of truth

`OddGnomonLayer` now has the definition:

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  DkMath.Gnomon.oddGnomon n
```

The explicit compatibility theorem is:

```text
oddGnomonLayer_eq_oddGnomon
```

It is definitional (`rfl`) and marked `[simp]`.

## 4. Refactored square and odd-sum theorems

The following existing public theorem names were preserved and now source
their proofs from the neutral API:

```text
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
```

The shifted theorem now proceeds through:

```text
DkMath.Gnomon.square_add_squareGnomonBand
DkMath.Gnomon.squareGnomonBand_eq_sum_shifted_oddGnomon
```

and retains its original `(P + u)^2` and
`2 * (P + i) + 1` statement.

## 5. Collatz-specific API preservation

The following definitions and theorem statements were not moved or changed:

```text
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
RawGnomonRemainderAtDepth
FirstFailedPow2Depth
rawGnomonHeight_eq_s
rawGnomonResidualShape_eq_T_val
rawGnomonResidualShape_odd
rawGnomonStep_eq_pow_height_mul_residualShape
two_pow_succ_rawGnomonHeight_not_dvd
rawGnomonRemainderAtDepth_eq_zero_of_le_height
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

`RawGnomonStep` still reduces through the neutral layer to
`n + (2*n + 1) = 3*n + 1`; the existing `threeNPlusOne`, `s`, and `T`
bridges continue to compile.

Compatibility regressions in the production file kernel-check:

```text
OddGnomonLayer 0 = 1
OddGnomonLayer 1 = 3
OddGnomonLayer 30 = 61
```

The general regressions remain covered by the preserved theorem statements
`rawGnomonStep_eq_three_mul_add_one` and
`square_add_eq_square_add_gnomon_sum`.

## 6. Validation

Run from `lean/dk_math`:

```text
lake build DkMath.Collatz.GnomonEvaluation
Build completed successfully (8661 jobs).

lake build DkMath.Collatz.Collatz2K26
Build completed successfully (8828 jobs).

lake build DkMath.Gnomon
Build completed successfully (8658 jobs).

git diff --check
passed with no diagnostics.
```

The requested command `lake build DkMath.Collatz` cannot resolve in this
checkout because there is no `DkMath/Collatz.lean` facade.  No facade was
added because GNIP-002 calls for the smallest compatibility change; the
concrete downstream Collatz aggregate `DkMath.Collatz.Collatz2K26` was built
instead and passed.

The changed Lean source was scanned for `sorry`, `admit`, and `axiom`; no
matches were found and no axiom was added.

The focused builds emitted no new warning.  The downstream Collatz aggregate
replayed the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`:
`declaration uses \`sorry\``.  This warning is outside GNIP-002 and was not
modified.

## 7. Compatibility issues

No semantic or elaboration compatibility issue was encountered.  The only
validation limitation is the absent `DkMath.Collatz` facade target described
above.

## 8. GNIP-003 status

GNIP-003 is now cleanly justified in principle: the neutral odd gnomon source
and its exact degree-two Cosmic bridge are available without importing
Collatz into the neutral layer, and the legacy Collatz names remain stable.
The Legendre open-gnomon bridge itself remains unimplemented here, with no
prime-support, cover, or existence claim added.
