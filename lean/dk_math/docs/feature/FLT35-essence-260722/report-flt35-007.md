# FLT5 full standalone provenance package report

- Date: 2026-07-22
- Checkpoint: F35-007
- Outcome: **B, corrected and completed**

## Result

The completed production FLT5 tower is now tracked as a reproducible,
Mathlib-only standalone artifact. The first staged audit found one
packaging-only issue: the reviewed generator emitted an extra blank line at
EOF, which failed `git diff --cached --check` although Lean accepted the file.

The artifact was not hand-edited. The generator was corrected to emit exactly
one terminal newline and committed first as `3aac6391`. The worktree was then
clean, and the complete package was regenerated from that exact source
snapshot. Comparator equivalence and formal axiom auditing remain F35-008.

## Verified runtime boundary

F35-007 PASS scope: **Lean/Mathlib v4.29.0 project environment**.

```text
lean-toolchain: leanprover/lean4:v4.29.0
lean-toolchain blob: 14791d727f9a9455fb1e828c6ce6c07fae007990
lake-manifest.json blob: 12106850f78e74c6451ae91cc91fd1597b2a1fc9
mathlib inputRev: v4.29.0
mathlib rev: 8a178386ffc0f5fef0b77738bb5449d50efeea95
```

The actual executable check was:

```text
command: lake env lean --version
output: Lean (version 4.29.0, x86_64-unknown-linux-gnu, commit 98dc76e3c0a9b856c9b98726b713fb04fab16740, Release)
```

The exact artifact bytes were rebuilt successfully as
`/tmp/FLT5#StandAlone-v0.v429.build.lean` in this environment. Lean/Mathlib
v4.32.0+ status was not tested here and is not claimed. Comparator Live is
deferred to a standalone-only compatibility checkpoint.

## Source snapshot

- Source commit SHA: `3aac63916dd78b15ed5aafdc16b41687d7877357`
- Source branch: `feature/FLT35-essence-260722-v0`
- Generator blob SHA: `7a4dd7499a913b2ed1d3603c019328b726adc1aa`
- Manifest blob SHA: `4ed51f935fd41557363009c1dc446d7dbf9bb82a`

The generated header contains exactly this commit SHA. No F35-007 package file
existed in the worktree when the source identity was recorded.

## Artifact

- Path: `DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt`
- Lines: 5981
- Bytes: 234552
- SHA-256: `400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd`

Independent generation to the tracked path and
`/tmp/FLT5#StandAlone-v0.verify.lean` was byte-identical (`cmp` exit 0).

## Integrity checks

Header provenance: PASS.

```text
Repository: Deskuma/dkmath
Branch: feature/FLT35-essence-260722-v0
Source commit SHA: 3aac63916dd78b15ed5aafdc16b41687d7877357
Manifest: DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt
Ordered source modules: 33
```

Import surface and declaration integrity: PASS.

```text
active imports total: 1
import Mathlib: 1
active import DkMath.*: 0
TraceOneBridge references: 0
theorem flt5Target: 1
theorem fermatFive_no_positive_solution: 1
BEGIN markers: 33
END markers: 33
```

## Build and checksum

Exact-byte isolated build: PASS.

```text
lake env lean /tmp/FLT5#StandAlone-v0.build.lean
exit_status: 0
```

Saved log:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log
```

Checksum verification: PASS.

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt: OK
```

## Production regression

`lake build DkMath.FLT.Five`: PASS.

No production theorem, proof file, manifest, or aggregator was modified. The
archival artifact remains outside the production import graph.

## Files changed

Packaging correction source commit:

```text
scripts/generate-flt5-standalone.py
```

F35-007 provenance package:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
docs/feature/FLT35-essence-260722/report-flt35-007.md
```

## Exact non-goals

This checkpoint does not modify FLT3 or FLT5 production proofs,
`TraceOneQuadratic`, either bridge, `GoldenInt`, or the GN5 seed standalone. It
does not import the artifact, add comparator wrappers, append `#print axioms`,
perform F35-008, update the main README, add p=7, or make a general-prime claim.

## Next recommended checkpoint

Proceed in the following sequence without changing this v4.29.0 provenance
artifact:

```text
F35-008A: v4.29.0 public/standalone statement comparison and axiom/trust audit
F35-008B: standalone-only Lean/Mathlib v4.32.0+ compatibility migration and Comparator Live validation
F35-009: documentation closure
```

F35-008B must remain isolated from any repository-wide Lean upgrade. A
Comparator-specific derivative may be patched or regenerated there, but it
must not silently redefine the pinned v4.29.0 artifact.
