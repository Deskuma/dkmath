# Codex instruction: F35-006 FLT5 standalone manifest and generator

## 0. Working context

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
feature/FLT35-essence-260722-v0
```

Read first:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/README.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-001.md
```

Current completed scope:

```text
F35-002 TraceOneQuadratic core
F35-003 FLT3 bridge
F35-004 FLT5 bridge
F35-005 facade and audit
```

This checkpoint is **F35-006 only**.

Do not implement F35-007 or commit the large generated standalone proof artifact yet.

## 1. Goal

Create a provenance-sensitive, deterministic source manifest and generator for a future Mathlib-only full FLT5 standalone file.

The generator must flatten the already completed production FLT5 module tower without changing theorem statements or proof bodies.

The target future artifact is:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
```

F35-006 prepares and validates generation infrastructure only.

## 2. Required new files

Create:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
lean/dk_math/scripts/generate-flt5-standalone.py
```

Create a report:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-006.md
```

Do not add the final `FLT5#StandAlone-v0.lean.txt` artifact in this checkpoint.

Temporary generated files used for verification must not remain tracked.

## 3. Manifest contract

The manifest is the single source of truth for flatten order.

Use repository-relative Lean source paths, one path per non-empty line.

Allow comment lines beginning with `#`.

Initial intended module set:

```text
DkMath/FLT/Five/Basic.lean
DkMath/FLT/Five/GN5.lean
DkMath/FLT/Five/CleanChannel.lean
DkMath/FLT/Five/Reduction.lean
DkMath/FLT/Five/NormalForm.lean
DkMath/FLT/Five/BranchB.lean
DkMath/FLT/Five/Provider.lean
DkMath/FLT/Five/BranchA.lean
DkMath/FLT/Five/SignedBranchA.lean
DkMath/FLT/Five/SignedFiveAdic.lean
DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean
DkMath/FLT/Five/SquareGoldenBridge.lean
DkMath/FLT/Five/SquareGoldenNormalForm.lean
DkMath/FLT/Five/SignedSquareGoldenExceptional.lean
DkMath/FLT/Five/GoldenOrder.lean
DkMath/FLT/Five/GoldenDivisibility.lean
DkMath/FLT/Five/GoldenEuclidean.lean
DkMath/FLT/Five/SignedGoldenRamifierStripped.lean
DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean
DkMath/FLT/Five/SignedGoldenFifthPower.lean
DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean
DkMath/FLT/Five/GoldenCoprimeFactor.lean
DkMath/FLT/Five/SignedGoldenUnitClasses.lean
DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean
DkMath/FLT/Five/SignedGoldenZeroSector.lean
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean
DkMath/FLT/Five/GoldenUnitClassification.lean
DkMath/FLT/Five/SignedGoldenZeroSectorDescent.lean
DkMath/FLT/Five/SignedGoldenClosure.lean
DkMath/FLT/Five/SignedGoldenZeroSectorFinal.lean
DkMath/FLT/Five/Valuation.lean
DkMath/FLT/Five/Main.lean
```

This order is a hypothesis from the design document, not an instruction to trust blindly.

Audit the real direct imports of every listed source and correct the order when necessary.

If an FLT5 production dependency is missing, add it to the manifest at the correct topological position.

Do not include:

```text
DkMath/FLT/Five.lean
DkMath/FLT/Five/Standalone.lean
DkMathTest/*
```

The current `Standalone.lean` is a separate GN5 seed and duplicates definitions.

## 4. Import-graph validation

The generator must parse direct lines of the form:

```lean
import DkMath.FLT.Five.X
```

For dependencies inside the FLT5 production tower:

- every dependency must occur earlier in the manifest;
- missing internal dependencies are errors;
- duplicate manifest entries are errors;
- nonexistent source paths are errors.

Imports outside the FLT5 production tower are allowed only if they are Mathlib imports.

If a listed production source directly imports another `DkMath.*` module outside `DkMath.FLT.Five.*`, do not silently strip it and produce an invalid artifact.

Instead:

1. report the external DkMath dependency;
2. determine whether its required source must also be flattened;
3. stop F35-006 with an honest Outcome C report if a safe manifest closure requires a broader design.

The generator must never claim Mathlib-only closure without validating this condition.

## 5. Generator interface

The script must run from `lean/dk_math`.

Recommended interface:

```bash
python scripts/generate-flt5-standalone.py --check
python scripts/generate-flt5-standalone.py --output /tmp/FLT5Standalone.lean
```

Required behavior:

### `--check`

- parse manifest;
- validate path existence;
- validate uniqueness;
- validate internal topological order;
- identify all direct non-Mathlib imports;
- print a concise ordered module summary;
- write no repository files.

### `--output PATH`

- run all checks first;
- generate one UTF-8 Lean file at `PATH`;
- do not default to the tracked final artifact path;
- overwrite only the explicitly supplied output path.

Use Python standard library only.

Return nonzero exit status on every validation failure.

## 6. Flattening contract

Generated file header must record:

```text
Generated artifact warning
repository
branch
source commit SHA when available
manifest path
ordered source module list
```

The generated Lean source must begin with the smallest honest import surface.

Expected ideal header:

```lean
import Mathlib
```

However, do not hardcode this conclusion before import closure validation.

For each flattened source:

- remove `import ...` lines;
- remove `#print "file: ..."` markers;
- remove repeated top-level copyright headers;
- retain namespace declarations;
- retain doc comments;
- retain definitions, theorem statements, and proofs verbatim;
- add a generated separator comment naming the source path.

Do not perform semantic rewriting.

Do not rename declarations.

Do not rewrite tactics.

Do not deduplicate declarations by theorem name. Duplicate declarations are a manifest/design error and must stop generation.

## 7. Determinism check

Generate twice to two temporary paths and verify byte-for-byte identity.

Example:

```bash
python scripts/generate-flt5-standalone.py --output /tmp/flt5-a.lean
python scripts/generate-flt5-standalone.py --output /tmp/flt5-b.lean
cmp /tmp/flt5-a.lean /tmp/flt5-b.lean
```

The report must record the result.

Do not include current wall-clock time in the generated file because it breaks determinism.

A source commit SHA is allowed because it is stable for the source snapshot.

## 8. Isolated smoke build

F35-006 should attempt a temporary isolated build only after generation succeeds.

```bash
lake env lean /tmp/flt5-a.lean
```

This is a smoke test of the generator contract, not yet the provenance package of F35-007.

If the generated source fails because the manifest is not dependency-closed, inspect and correct the manifest.

If satisfying dependency closure requires flattening a large non-FLT5 DkMath subsystem, stop and report Outcome C rather than broadening scope silently.

Do not commit `/tmp/flt5-a.lean` or a copied final artifact.

## 9. Endpoint presence checks

The generated temporary source must contain exactly one declaration of each endpoint:

```text
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

The script may perform textual declaration-count checks for these names.

Do not add a new endpoint wrapper in F35-006.

## 10. Explicit non-goals

Do not:

- edit existing FLT3 or FLT5 theorem statements;
- edit proof bodies in production modules;
- refactor `GoldenInt`;
- refactor `ThreeTraceOneBridge` imports;
- add the $p=7$ experiment;
- add a general odd-prime theorem;
- add the final tracked standalone artifact;
- change `DkMath.FLT.Five.Standalone` seed;
- add the standalone file to any production aggregator.

## 11. Verification

Run at minimum:

```bash
cd lean/dk_math
python scripts/generate-flt5-standalone.py --check
python scripts/generate-flt5-standalone.py --output /tmp/flt5-a.lean
python scripts/generate-flt5-standalone.py --output /tmp/flt5-b.lean
cmp /tmp/flt5-a.lean /tmp/flt5-b.lean
lake env lean /tmp/flt5-a.lean
lake build DkMath.FLT.Five
```

Also run:

```bash
git diff --check
```

## 12. Outcome branches

### Outcome A

Manifest closes over Mathlib plus the listed FLT5 production files, generation is deterministic, and temporary isolated build passes.

Commit manifest, generator, and report only.

### Outcome B

Manifest/order bugs are found but can be corrected within the FLT5 production tower.

Correct them, verify, and commit manifest, generator, and report.

### Outcome C

The FLT5 tower has direct external `DkMath.*` dependencies whose safe flattening materially broadens the project.

Do not fake a Mathlib-only result.

Commit the validator and an honest report describing:

- exact external dependencies;
- first failing source files;
- minimal closure options;
- recommended F35-006b design.

Do not commit the large generated artifact.

## 13. Report contract

`report-flt35-006.md` must include:

- final manifest order;
- all direct external imports found;
- validation method;
- deterministic generation result;
- temporary output line count and byte size;
- isolated Lean smoke-build result;
- endpoint declaration counts;
- files changed;
- exact outcome A, B, or C;
- next recommended checkpoint.

## 14. Commit boundary

One implementation commit is preferred.

Suggested commit message:

```text
Add FLT5 standalone manifest generator
```

Push the completed checkpoint to:

```text
feature/FLT35-essence-260722-v0
```
