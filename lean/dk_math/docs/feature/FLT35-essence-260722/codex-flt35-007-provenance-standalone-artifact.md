# Codex instruction: F35-007 FLT5 tracked standalone provenance package

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
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-006.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
lean/dk_math/scripts/generate-flt5-standalone.py
```

F35-006 completed with Outcome A:

```text
33 production modules
no external DkMath imports
deterministic generation
Mathlib-only isolated build PASS
```

This checkpoint is **F35-007 only**.

Comparator statement equivalence and full trust/axiom audit remain F35-008.

## 1. Goal

Generate and track the completed Mathlib-only FLT5 standalone proof artifact from the reviewed manifest and generator.

Preserve exact provenance for the source snapshot used to generate it.

Do not manually edit the generated Lean artifact.

## 2. Required tracked files

Create:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
```

Do not alter the existing manifest unless generation validation now fails.

Do not alter production theorem files.

Do not import the standalone artifact from any DkMath module.

## 3. Source snapshot Core

Start from a clean worktree.

Before generating the artifact, record:

```bash
SOURCE_COMMIT=$(git rev-parse HEAD)
SOURCE_BRANCH=$(git branch --show-current)
```

The source commit must be the exact parent state containing:

- the completed FLT5 production tower;
- the reviewed manifest;
- the reviewed generator;
- this F35-007 instruction.

Generate before committing any F35-007 output files.

The generated artifact header must contain exactly this `SOURCE_COMMIT` as its `Source commit SHA`.

Do not regenerate after the F35-007 artifact commit, because that would rewrite the header to the artifact commit itself and destroy the parent-snapshot provenance relation.

## 4. Pre-generation validation

From `lean/dk_math`, run:

```bash
python scripts/generate-flt5-standalone.py --check
```

Require:

```text
modules: 33
external non-Mathlib imports: none
DkMath.FLT.Five.flt5Target = 1
DkMath.FLT.Five.fermatFive_no_positive_solution = 1
```

If this validation fails, stop and report rather than creating a tracked artifact.

## 5. Deterministic generation

Set paths:

```bash
ARTIFACT='DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt'
TMP_ARTIFACT='/tmp/FLT5#StandAlone-v0.verify.lean'
```

Generate twice from the same clean source snapshot:

```bash
python scripts/generate-flt5-standalone.py --output "$ARTIFACT"
python scripts/generate-flt5-standalone.py --output "$TMP_ARTIFACT"
cmp "$ARTIFACT" "$TMP_ARTIFACT"
```

Require byte-for-byte equality.

Expected approximate measurement from F35-006:

```text
5982 lines
234553 bytes
```

A difference is not automatically a failure, but it must be explained by a reviewed source change. With no production or generator changes, the values should remain identical.

## 6. Header provenance verification

Verify the tracked artifact header records:

```text
Repository: Deskuma/dkmath
Branch: feature/FLT35-essence-260722-v0
Source commit SHA: <SOURCE_COMMIT>
Manifest: DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
```

Verify the ordered module list has 33 entries.

Verify the only active import in the generated artifact is:

```lean
import Mathlib
```

Generated source separator comments containing source paths are expected and are not imports.

## 7. Isolated Lean build and saved log

A `.lean.txt` path is an archival artifact, so build an exact byte copy with a `.lean` suffix.

```bash
BUILD_COPY='/tmp/FLT5#StandAlone-v0.build.lean'
BUILD_LOG='DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log'
cp "$ARTIFACT" "$BUILD_COPY"
```

Create a useful saved log containing provenance metadata, the command, output, and exit status.

Use `pipefail` so a failing Lean command cannot be hidden by `tee`.

Suggested form:

```bash
set -o pipefail
{
  echo "artifact: $ARTIFACT"
  echo "source_commit: $SOURCE_COMMIT"
  echo "source_branch: $SOURCE_BRANCH"
  echo "command: lake env lean $BUILD_COPY"
  lake env lean "$BUILD_COPY"
  STATUS=$?
  echo "exit_status: $STATUS"
  exit $STATUS
} 2>&1 | tee "$BUILD_LOG"
```

Require:

```text
exit_status: 0
```

Do not hand-edit Lean output in the saved log.

## 8. Checksum

Generate the checksum from the final tracked artifact bytes.

```bash
CHECKSUM='DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
sha256sum "$ARTIFACT" > "$CHECKSUM"
sha256sum --check "$CHECKSUM"
```

Run the command from `lean/dk_math` so the filename recorded in the checksum file is stable and repository-relative.

The checksum file must contain exactly one artifact entry.

## 9. Provenance document

Create:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
```

Record at minimum:

- repository;
- branch;
- source commit SHA;
- generator path;
- generator Git blob SHA at `SOURCE_COMMIT`;
- manifest path;
- manifest Git blob SHA at `SOURCE_COMMIT`;
- ordered source count: 33;
- artifact path;
- artifact SHA-256;
- line count;
- byte count;
- isolated build command;
- isolated build result;
- production endpoint names;
- statement that the artifact is generated and must not be manually edited;
- statement that it is not imported by DkMath production modules;
- statement that F35-008 will perform comparator and axiom/trust audit.

Obtain blob SHAs from the source snapshot, for example from the repository root:

```bash
GENERATOR_BLOB=$(git rev-parse "$SOURCE_COMMIT:lean/dk_math/scripts/generate-flt5-standalone.py")
MANIFEST_BLOB=$(git rev-parse "$SOURCE_COMMIT:lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt")
```

Do not record an uncommitted working-tree hash as the source identity.

## 10. Artifact integrity checks

Require all of the following:

```text
exactly one active import: Mathlib
exactly one theorem declaration: flt5Target
exactly one theorem declaration: fermatFive_no_positive_solution
33 generated source BEGIN markers
33 generated source END markers
no active import DkMath.*
no reference to DkMath.FLT.Five.TraceOneBridge
```

The last exclusion is intentional: `TraceOneBridge` is an observational feature bridge, not part of the completed standalone FLT5 proof provenance.

Do not use a naive search for the substring `sorry`, because comments may contain explanatory text. F35-008 will perform the formal axiom audit.

## 11. Production regression check

Run:

```bash
lake build DkMath.FLT.Five
```

The standalone file must remain outside the production import graph.

Confirm no production aggregator was modified to import it.

## 12. Report contract

Create:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
```

Include:

- checkpoint and outcome;
- source commit SHA;
- generator and manifest blob SHAs;
- generated artifact path;
- line and byte counts;
- artifact SHA-256;
- deterministic comparison result;
- header provenance result;
- import-surface result;
- endpoint declaration counts;
- BEGIN/END source marker counts;
- isolated Lean build result and log path;
- checksum verification result;
- production regression build result;
- files changed;
- exact non-goals;
- next recommended checkpoint F35-008.

## 13. Explicit non-goals

Do not:

- modify any FLT3 proof;
- modify any FLT5 production proof;
- modify `TraceOneQuadratic` or either bridge;
- modify `DkMath.FLT.Five.Standalone` GN5 seed;
- add the generated artifact to an import aggregator;
- add a comparator challenge theorem;
- append `#print axioms` to the generated proof artifact;
- perform the F35-008 axiom audit;
- update the main README to completed status;
- add the $p=7$ experiment;
- make a general-prime claim.

## 14. Verification commands

Run at minimum:

```bash
cd lean/dk_math
python scripts/generate-flt5-standalone.py --check
python scripts/generate-flt5-standalone.py \
  --output 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt'
python scripts/generate-flt5-standalone.py \
  --output '/tmp/FLT5#StandAlone-v0.verify.lean'
cmp \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' \
  '/tmp/FLT5#StandAlone-v0.verify.lean'
cp \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' \
  '/tmp/FLT5#StandAlone-v0.build.lean'
lake env lean '/tmp/FLT5#StandAlone-v0.build.lean'
sha256sum \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' \
  > 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
lake build DkMath.FLT.Five
git diff --check
```

## 15. Outcome branches

### Outcome A

Tracked artifact is reproducible, provenance is exact, checksum verifies, isolated build passes, and production build remains unchanged.

Commit all F35-007 package files and report.

### Outcome B

A packaging-only issue is found in log/checksum/provenance handling, while the generated Lean artifact itself remains valid.

Correct the packaging issue, rerun all checks, and commit.

### Outcome C

Generated output no longer matches the reviewed source closure, isolated build fails, source SHA is inconsistent, or fixing the issue would require production proof changes.

Do not commit a misleading artifact package.

Report the exact first failure and stop for redesign.

## 16. Commit boundary

One implementation commit is preferred.

Suggested commit message:

```text
Add FLT5 full standalone provenance package
```

Push to:

```text
feature/FLT35-essence-260722-v0
```
