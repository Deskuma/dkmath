# Gate011 verification summary

Provenance: **Codex-reported**, locally executed2026-10-13; not independently reproduced.
Environment: Lean4.34.1 /Lake5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean`: exit **0**, no warning/error.

```text
Build completed successfully (9091 jobs).
```

Actual test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion
'DkMath.FLT.Seven.eligible_primitive_divisor_two_thirteen_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_thirteen_power_family_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.thirteenPowerCore_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.coprimality_guard_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Primitive coprime allocation of2*13^n forces r1/r2 for all n, including0. Euclid and the coarse guard replace the global size cutoff. Existing mod42/mod5 consumers exclude the full sieve for every k at2*13^(6+4*k).
Tests prove injectivity of the index map, recover9653618 at k0, check k1/k2, and fix the r13,n10 countermodel without the coprimality guard. No source-packet or exact endpoint witness is constructed.

Checked source SHA-256:

```text
5e8770a84eb27a29a30ba243229927afb37298b51d773e8e53faae5fd0242a74  DkMath/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean
77e4f037cc97b5e74ca21180087b9113fa851d6e8e606e9f8b25f40654a96c8c  DkMathTest/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean
```

Full API/proof/boundaries: [report-011.md](../report-011.md). Raw logs remain disposable. No Git mutation.
