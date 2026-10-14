# Gate 009 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Environment: Lean4.34.1 / Lake5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618 DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean`: exit **0**, no warning/error.

```text
Build completed successfully (9093 jobs).
```

Actual test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionCompositeCore9653618
'DkMath.FLT.Seven.eligible_divisor_9653618_eq_one_or_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSievedNestedCondition_9653618_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_9653618' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every divisor satisfying membership + coarse bound is1/2. Existing mod42 excludes the same selected r1 with its explicit divisibility guard; existing mod5 excludes r2. The full exact sieve is false while the cheap existential remains true by r2. This is a single-core synthesis, not packet existence or global FLT7.

Checked source SHA-256:

```text
a5cbf6787fe382839c1944c0d65331cdb46216822aa48e816e23868b3e2f73e9  DkMath/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean
209fcc57c1e5f75a28a3a5282394ddbc4f31467dfb0f987965958fba33996d5e  DkMathTest/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean
```

Full API, initial tactic repair and limits: [report-009.md](../report-009.md). Raw logs stay disposable. No Git mutation.
