# Gate 002 verification summary

Provenance: **Codex-reported**, locally executed on 2026-10-13; not an independent reviewer rerun.
Base commit: `ea54ced2652763208a47c3a16507a7235eb264f4`.
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00.

## Decisive validation

Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean`: exit **0** (all applications, counterexamples, power/CRT checks and axiom audit).

Build completion excerpt:

```text
Build completed successfully (9087 jobs).
```

The job count includes the single target's import dependencies; it is not a count of changed modules.
Actual test / audit output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve
'DkMath.FLT.Seven.nestedAllocation_mod_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_mod_fortyTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_fortyTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three exports retain `r ∣ M`. No `sorryAx` or nonstandard axiom appears.
The test fixes the unguarded coprimality transport counterexample `M=1,r=2,u=2`, without claiming its full receiver equation holds.
It also checks `M=1,r=1`: divisor and mod-42 filter hold, but neither receiver holds (existing threshold/size facts).
`M=8,r=1` is excluded by the new consumer; `589≡1 (mod 42)` alone supplies no witness.

## Checked source identity (SHA-256)

```text
ddfafa3f3fe19ba267c0ea05697d9210db1eb2f635674d733b65141ce032e191  DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean
2e4861102c2a4967c02cf87781c73fe80a32fb3bd7996f51a06516c7f1eefc6f  DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean
```

Full API and reasoning: [report-002.md](../report-002.md).
Raw transcripts remain ignored in `logs/`; none are part of this evidence artifact.
