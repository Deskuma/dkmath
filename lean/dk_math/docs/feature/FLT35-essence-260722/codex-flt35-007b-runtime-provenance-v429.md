# Codex instruction: F35-007b pin Lean v4.29 runtime provenance

## 0. Context

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
feature/FLT35-essence-260722-v0
```

Current artifact source snapshot:

```text
3aac63916dd78b15ed5aafdc16b41687d7877357
```

Current tracked artifact package commit:

```text
84133fcabbd9f16302c54736a918e4d23c989786
```

Read first:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log
lean/dk_math/lean-toolchain
lean/dk_math/lake-manifest.json
```

## 1. Review finding

F35-007 is mathematically and mechanically accepted **for the current project environment**.

That environment is version-pinned:

```text
Lean: v4.29.0
Mathlib input revision: v4.29.0
Mathlib Git revision: 8a178386ffc0f5fef0b77738bb5449d50efeea95
```

The standalone artifact imports only `Mathlib`, but this means only that its active import surface contains no `DkMath.*` import. It does **not** mean the artifact has been proved compatible with every later Lean/Mathlib release.

Lean Comparator Live requires Lean/Mathlib v4.32.0 or later. Compatibility with that environment is not part of F35-007 and must not be claimed here.

This checkpoint records the v4.29.0 runtime boundary explicitly without modifying the generated artifact.

## 2. Scope

Update only:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
```

Do not modify:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
lean/dk_math/scripts/generate-flt5-standalone.py
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
any production Lean source
```

The artifact SHA-256 must remain:

```text
400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

## 3. Runtime facts to record

Record the following source-controlled facts:

```text
lean-toolchain content: leanprover/lean4:v4.29.0
lean-toolchain Git blob SHA at source commit: 14791d727f9a9455fb1e828c6ce6c07fae007990
lake-manifest.json Git blob SHA at source commit: 12106850f78e74c6451ae91cc91fd1597b2a1fc9
mathlib inputRev: v4.29.0
mathlib rev: 8a178386ffc0f5fef0b77738bb5449d50efeea95
```

Verify the blob SHAs against the source snapshot before recording them:

```bash
SOURCE_COMMIT=3aac63916dd78b15ed5aafdc16b41687d7877357

git rev-parse "$SOURCE_COMMIT:lean/dk_math/lean-toolchain"
git rev-parse "$SOURCE_COMMIT:lean/dk_math/lake-manifest.json"
```

Also capture the actual executable version used by the current environment:

```bash
cd lean/dk_math
lake env lean --version
```

The result must identify Lean 4.29.0. If it does not, stop and report the environment mismatch.

## 4. Provenance document update

Add a section such as:

```text
## Verified build environment
```

It must state:

- the artifact was generated and built under Lean v4.29.0;
- the exact `lean-toolchain` content and blob SHA;
- the exact `lake-manifest.json` blob SHA;
- the exact Mathlib input revision and resolved Git revision;
- the command used to obtain the executable version;
- the actual version output;
- the build result applies to this pinned environment;
- no compatibility claim is made for Lean/Mathlib v4.32.0 or later;
- Comparator Live compatibility will be handled in a separate standalone-only migration checkpoint.

Do not weaken the existing source commit, generator blob, manifest blob, artifact checksum, or endpoint provenance.

## 5. Build-log update

Regenerate or extend the saved build log so it records the pinned environment before the existing build command.

Required fields:

```text
artifact
source_commit
source_branch
lean_toolchain
lean_toolchain_blob
lake_manifest_blob
mathlib_input_rev
mathlib_rev
lean_version_command
lean_version_output
build_command
exit_status
```

Use the current project v4.29.0 environment and rebuild the exact artifact bytes through a temporary `.lean` copy:

```bash
cd lean/dk_math
ARTIFACT='DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt'
BUILD_COPY='/tmp/FLT5#StandAlone-v0.v429.build.lean'
BUILD_LOG='DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log'
cp "$ARTIFACT" "$BUILD_COPY"
```

Run `lake env lean --version`, then `lake env lean "$BUILD_COPY"`, preserving the real exit status with `set -o pipefail`.

Do not fabricate or normalize the version output beyond placing it on a clearly identified log line.

## 6. Report update

Update `report-flt35-007.md` with a version-boundary section.

State precisely:

```text
F35-007 PASS scope: Lean/Mathlib v4.29.0 project environment
v4.32.0+ status: not tested here and not claimed
Comparator Live: deferred to standalone-only compatibility checkpoint
```

Retain Outcome B, corrected and completed.

Do not reclassify the EOF correction or regenerate the artifact.

## 7. Verification

Run:

```bash
cd lean/dk_math
lake env lean --version
cp \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' \
  '/tmp/FLT5#StandAlone-v0.v429.build.lean'
lake env lean '/tmp/FLT5#StandAlone-v0.v429.build.lean'
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
lake build DkMath.FLT.Five
git diff --check
```

Confirm:

```text
Lean version = 4.29.0
artifact checksum unchanged
isolated build PASS under v4.29.0
production build PASS
artifact file unchanged
checksum file unchanged
```

Use `git diff --exit-code --` on the artifact and checksum paths against the current branch parent to prove they were not modified.

## 8. Future checkpoint split

Record the following sequencing in the report, without implementing it now:

```text
F35-008A: v4.29.0 public/standalone statement comparison and axiom/trust audit
F35-008B: standalone-only Lean/Mathlib v4.32.0+ compatibility migration and Comparator Live validation
F35-009: documentation closure
```

F35-008B must be isolated from the repository-wide Lean upgrade. It may patch or regenerate a Comparator-specific standalone derivative, but it must not silently redefine the v4.29.0 provenance artifact.

## 9. Non-goals

Do not:

- modify the standalone Lean artifact;
- change its checksum;
- modify generator output rules;
- modify production proof code;
- attempt Lean v4.32.0 migration;
- run Comparator Live;
- perform axiom or statement comparison;
- update the main feature README to completed status.

## 10. Commit

One documentation/provenance commit.

Suggested message:

```text
Docs: pin FLT5 standalone Lean v4.29 provenance
```

Push to:

```text
feature/FLT35-essence-260722-v0
```
