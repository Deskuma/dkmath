# FLT5 Standalone v0 Provenance

This artifact is generated. Do not edit it manually; regenerate it from the
reviewed manifest and generator.

## Source identity

- Repository: `Deskuma/dkmath`
- Branch: `feature/FLT35-essence-260722-v0`
- Source commit SHA: `3aac63916dd78b15ed5aafdc16b41687d7877357`
- Generator: `lean/dk_math/scripts/generate-flt5-standalone.py`
- Generator Git blob SHA at source commit: `7a4dd7499a913b2ed1d3603c019328b726adc1aa`
- Manifest: `lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.manifest.txt`
- Manifest Git blob SHA at source commit: `4ed51f935fd41557363009c1dc446d7dbf9bb82a`
- Ordered source count: 33

The source commit is the exact clean parent snapshot containing the completed
FLT5 tower, manifest, generator, and instruction. It includes the packaging-only
EOF normalization found during F35-007, and the generated header records this
same source commit.

## Artifact identity

- Artifact: `lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt`
- SHA-256: `400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd`
- Line count: 5981
- Byte count: 234552
- Active import surface: `import Mathlib`

Production endpoints included exactly once:

- `DkMath.FLT.Five.flt5Target`
- `DkMath.FLT.Five.fermatFive_no_positive_solution`

## Build verification

- Exact-byte build copy: `/tmp/FLT5#StandAlone-v0.build.lean`
- Command: `lake env lean /tmp/FLT5#StandAlone-v0.build.lean`
- Result: PASS (`exit_status: 0`)
- Saved log: `lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.build.log`

## Verified build environment

The artifact was generated and built in the version-pinned project environment:

- Lean toolchain: `leanprover/lean4:v4.29.0`
- `lean-toolchain` Git blob SHA at source commit:
  `14791d727f9a9455fb1e828c6ce6c07fae007990`
- `lake-manifest.json` Git blob SHA at source commit:
  `12106850f78e74c6451ae91cc91fd1597b2a1fc9`
- Mathlib input revision: `v4.29.0`
- Mathlib resolved Git revision:
  `8a178386ffc0f5fef0b77738bb5449d50efeea95`
- Version command: `lake env lean --version`
- Version output: `Lean (version 4.29.0, x86_64-unknown-linux-gnu, commit
  98dc76e3c0a9b856c9b98726b713fb04fab16740, Release)`

The successful build applies to this pinned Lean/Mathlib v4.29.0 environment.
No compatibility claim is made for Lean/Mathlib v4.32.0 or later. Lean
Comparator Live compatibility is deferred to a separate standalone-only
migration checkpoint; it will not silently redefine this v4.29.0 provenance
artifact.

The standalone artifact is archival and is not imported by any DkMath
production module. It excludes the observational `TraceOneBridge` and the
separate `DkMath.FLT.Five.Standalone` GN5 seed.

F35-008A will separately perform the v4.29.0 public/standalone statement
comparison and formal axiom/trust audit. Those claims are not part of this
provenance record.
