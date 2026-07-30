# FLT5 standalone manifest and generator report

- Date: 2026-07-22
- Checkpoint: F35-006
- Outcome: **A**

## Result

The production FLT5 tower closes over 33 manifest sources plus Mathlib.  No
direct external `DkMath.*` dependency was found.  The new generator validates
the closure and topological order, produces deterministic UTF-8 Lean source,
and the temporary flattened source passes an isolated Lean smoke build.

The final tracked `FLT5#StandAlone-v0.lean.txt` artifact was deliberately not
created; that remains F35-007.

## Final manifest order

```text
01 DkMath/FLT/Five/Basic.lean
02 DkMath/FLT/Five/GN5.lean
03 DkMath/FLT/Five/CleanChannel.lean
04 DkMath/FLT/Five/Reduction.lean
05 DkMath/FLT/Five/NormalForm.lean
06 DkMath/FLT/Five/BranchB.lean
07 DkMath/FLT/Five/Provider.lean
08 DkMath/FLT/Five/BranchA.lean
09 DkMath/FLT/Five/SignedBranchA.lean
10 DkMath/FLT/Five/SignedFiveAdic.lean
11 DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean
12 DkMath/FLT/Five/SquareGoldenBridge.lean
13 DkMath/FLT/Five/SquareGoldenNormalForm.lean
14 DkMath/FLT/Five/SignedSquareGoldenExceptional.lean
15 DkMath/FLT/Five/GoldenOrder.lean
16 DkMath/FLT/Five/GoldenDivisibility.lean
17 DkMath/FLT/Five/GoldenEuclidean.lean
18 DkMath/FLT/Five/SignedGoldenRamifierStripped.lean
19 DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean
20 DkMath/FLT/Five/SignedGoldenFifthPower.lean
21 DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean
22 DkMath/FLT/Five/GoldenCoprimeFactor.lean
23 DkMath/FLT/Five/SignedGoldenUnitClasses.lean
24 DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean
25 DkMath/FLT/Five/SignedGoldenZeroSector.lean
26 DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
27 DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean
28 DkMath/FLT/Five/GoldenUnitClassification.lean
29 DkMath/FLT/Five/SignedGoldenZeroSectorDescent.lean
30 DkMath/FLT/Five/SignedGoldenClosure.lean
31 DkMath/FLT/Five/SignedGoldenZeroSectorFinal.lean
32 DkMath/FLT/Five/Valuation.lean
33 DkMath/FLT/Five/Main.lean
```

This order was checked against every direct
`import DkMath.FLT.Five.X` line rather than accepted from the initial design
hypothesis.

## Direct external imports

All direct imports outside the manifest were Mathlib imports:

```text
Mathlib
Mathlib.Algebra.Order.Round
Mathlib.RingTheory.EuclideanDomain
Mathlib.NumberTheory.Zsqrtd.Basic
```

Direct external `DkMath.*` imports: **none**.

The excluded `DkMath/FLT/Five/TraceOneBridge.lean` has a neutral DkMath
dependency, but it is an observational bridge added after the completed proof
tower and is not imported by `Main.lean`; it is correctly outside the full FLT5
proof manifest.  The aggregator, the existing `Standalone.lean` GN5 seed, and
all `DkMathTest` sources are also excluded by contract.

## Validation method

`scripts/generate-flt5-standalone.py` uses only the Python standard library. It:

1. reads nonempty, non-comment manifest lines;
2. rejects unsafe, duplicate, forbidden, and nonexistent paths;
3. parses direct Lean import lines;
4. requires every internal FLT5 dependency to occur earlier;
5. rejects any non-Mathlib import outside the manifest closure;
6. strips imports, file markers, and repeated leading copyright blocks;
7. retains namespace declarations, documentation, declarations, and proofs;
8. records repository, branch, commit SHA, manifest, and ordered sources;
9. requires exactly one textual declaration of each public endpoint;
10. writes only an explicitly supplied output path.

The generated source has the validated minimal import surface:

```lean
import Mathlib
```

## Verification results

Commands were run from `lean/dk_math`.

```text
python scripts/generate-flt5-standalone.py --check
```

Result: PASS; 33 modules, no external DkMath import, both endpoint counts equal
to one.

```text
python scripts/generate-flt5-standalone.py --output /tmp/flt5-a.lean
python scripts/generate-flt5-standalone.py --output /tmp/flt5-b.lean
cmp /tmp/flt5-a.lean /tmp/flt5-b.lean
```

Result: PASS; byte-for-byte identical.

Temporary output measurements:

```text
lines: 5982
bytes: 234553
```

Endpoint declaration counts:

```text
DkMath.FLT.Five.flt5Target = 1
DkMath.FLT.Five.fermatFive_no_positive_solution = 1
```

```text
lake env lean /tmp/flt5-a.lean
```

Result: PASS.  The flattened source builds with Mathlib only.

```text
lake build DkMath.FLT.Five
```

Result: PASS.  The production FLT5 package remains unchanged and builds.

## Files changed in F35-006

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
scripts/generate-flt5-standalone.py
docs/feature/FLT35-essence-260722/report-flt35-006.md
```

No production theorem statement or proof body was edited.  No generated proof
artifact was added to the repository.

## Next recommended checkpoint

Proceed to F35-007 under a separate review instruction: generate the tracked
artifact from this manifest, repeat the isolated build, save the build log and
SHA-256 checksum, and preserve exact provenance.  Comparator and trust audit
remain F35-008.
