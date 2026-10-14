# Gate012 verification summary

Provenance: **Codex-reported**, locally executed2026-10-13; not independently reproduced.
Environment: Lean4.34.1 /Lake5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion` (final): exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean` (final): exit **0**, no warning/error.

```text
Build completed successfully (9091 jobs).
```

Actual final test/axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion
'DkMath.FLT.Seven.eligible_primitive_divisor_two_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_two_prime_pow_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Generic structure retains prime/membership/actual quotient coprimality/size. Full-sieve exclusion is conditional on the two residues, with no upper bound. Tests recover13 family and independently verify223,n2,M99458, including nonvacuous r2 eligibility. Prior coprimality-guard countermodel is reused; a checked composite s=3*5^10 permits primitive eligible r3, so the classification does not extend to all composites.
No source-packet or sixth-power witness is inferred from eligibility.

Checked source SHA-256:

```text
99321c2366028cad0f9912c2a03e19aed3a4073da202bee6bed0a43531600599  DkMath/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean
2d1be36244ee0218067bb672669be0f870316721675f4a852c55314e65818080  DkMathTest/FLT/Seven/SevenRamifiedFusionPrimePowerPrimitiveExclusion.lean
```

FullAPI/repairs/scope: [report-012.md](../report-012.md). Raw logs remain disposable. No Git mutation.
