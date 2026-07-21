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

The standalone artifact is archival and is not imported by any DkMath
production module. It excludes the observational `TraceOneBridge` and the
separate `DkMath.FLT.Five.Standalone` GN5 seed.

F35-008 will separately perform public/standalone statement comparison and the
formal axiom/trust audit. Those claims are not part of this provenance record.
