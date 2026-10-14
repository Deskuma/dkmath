# Gate 003 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not an independent reviewer rerun.
Base revision: `0d4f07b9188f55f95dedc7dd7600448b39687c70`.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00.
Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean`: exit **0**, no warnings/errors.

Decisive build excerpt:

```text
Build completed successfully (9089 jobs).
```

Actual test and axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation
'DkMath.FLT.Seven.sixthPowerSieved_implies_mod42Cheap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_implies_mod42Cheap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.candidate554_old_guards' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.candidate554_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.candidate589_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Definitions are endpoint-free. Two production implications reuse the exact-to-mod42 bridge and existing reconstruction equivalence; no extra assumptions.
The fixed allocation `(M,r)=(554,1)` satisfies old necessary numeric guards plus the modulus-one sixth-power sieve, but fails the new filter. This does not assert the old exact predicate.
`(589,1)` passes the new filter. Passing it supplies no endpoint witness.
The general implication from new numeric filter to old numeric guards is also tested; sixth-power existence stays separate.

Checked source SHA-256:

```text
81ab07261db74e3dcaee06d3b1ab1098a9913905a7e15acc3e67ab080c7e7c1a  DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean
760c101e3061a135d15cf6a1c8578e53655e60011e50aa3f6de9a7e7dacb18d5  DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean
```

Full statements and boundaries: [report-003.md](../report-003.md).
Raw output stays disposable in ignored `logs/`. No Git mutation is part of this gate.
