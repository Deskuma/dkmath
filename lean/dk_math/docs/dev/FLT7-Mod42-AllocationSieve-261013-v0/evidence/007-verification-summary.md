# Gate 007 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean`: exit **0**, no warning/error.

```text
Build completed successfully (9092 jobs).
```

Actual final test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage
'DkMath.FLT.Seven.centeredSevenSextic_fixedGap_mod_five_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.centeredSevenSextic_fixedGap_no_image_mod_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_one_excluded_of_mod_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_modFive_family' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The actual fixed-gap image is included in {1,2,4}; test witnesses attain all three. The private target identity holds for all s; s≡1 yields target3. For every k, the existing cheap/separate sixth-power filters hold at M=631+210*k,r=1 while the exact receiver fails. Injectivity and an explicit arbitrary-bound test confirm unboundedness.
At589, the target matches the mod-five image at q=1, while the existing adjacent-gap theorem still excludes a natural exact image. These are separate mechanisms.
No all-divisor exclusion for this progression or packet witness is claimed. No Python result is imported as a proof premise.

Checked source SHA-256:

```text
8a43d5772cc94171a0cfca504c012db74bb317725bf756624611e3135f698149  DkMath/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean
6032eafd573ae33e4e3473ff96e9ed423861ee304b7fcb81f5a77b18efaf751e  DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean
```

Exact API, failed tactic attempt and limits: [report-007.md](../report-007.md).
Raw logs are disposable. No Git mutation.
