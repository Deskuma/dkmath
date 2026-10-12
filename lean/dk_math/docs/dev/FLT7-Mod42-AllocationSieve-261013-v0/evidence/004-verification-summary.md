# Gate 004 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not an independent reviewer rerun.
Base revision: `41921e1bbe765b5e7721698f258ca6889a209e9a`.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean` (final version): exit **0**, no warning/error.

Build completion:

```text
Build completed successfully (9091 jobs).
```

Actual final test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit
'DkMath.FLT.Seven.no_mod42Cheap_at_554' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family_has' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family_sixthPower' depends on axioms: [propext]
'DkMath.FLT.Seven.mod42Cheap_survivors_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_554' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

554 has no cheap divisor allocation. For every bound B, the theorem chooses index k=B and produces a larger core 631+42*k passing the cheap filter and the separate modulus-one sixth-power condition. Family injectivity and the gate-003 survivor 589 are tested. No packet or exact endpoint witness is asserted.

Checked source SHA-256:

```text
40a82be7151efe94619e5e2435c8224d71caf88b41b696606054057273ec1646  DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean
f58e302040342a9d97972748c157bf9152e1c1e1a7b7b9e5660707e2bf6df6dc  DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean
```

Full API, failed tactic attempts and limits: [report-004.md](../report-004.md).
Raw transcripts stay disposable in ignored `logs/`. No Git mutation.
