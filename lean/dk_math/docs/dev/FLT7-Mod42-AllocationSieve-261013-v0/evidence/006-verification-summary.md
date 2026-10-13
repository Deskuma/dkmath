# Gate 006 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Base revision: `b5566b24463a78024be811253bf1372862cad295`.
Environment: Lean 4.34.1 / Lake 5.0.0-src+5045d00. Cwd: `lean/dk_math`.

## Python precheck (not a Lean proof)

Executed `python3 docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/logs/006-precheck.py`: exit **0**.
Exact code:

```python
D = 7**27
k = 52382010648825907313680
T = 448*589**49
def F(q):
    return 7*q**6 + 35*D**2*q**4 + 21*D**4*q**2 + D**6
assert D == 65712362363534280139543
assert F(k) < T < F(k+1)
print('Python precheck only: D matches; F(k)<T=True; T<F(k+1)=True')
print('Positive gap decimal digits:', len(str(T-F(k))), len(str(F(k+1)-T)))
```

Actual output:

```text
Python precheck only: D matches; F(k)<T=True; T<F(k+1)=True
Positive gap decimal digits: 117 116
```

## Lean proof acceptance

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589 DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean`: exit **0**, no warning/error.

```text
Build completed successfully (9093 jobs).
```

Actual final test / axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredImage589
'DkMath.FLT.Seven.centeredSevenSextic_589_bracket' depends on axioms: [propext]
'DkMath.FLT.Seven.centeredSevenSextic_589_no_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_589_one_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSievedNestedCondition_589_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_589' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The bracket is kernel-reduced from the actual polynomial; the Python output is not imported as a premise. Existing adjacent no-image and centered/exact equivalence transport it to exact receiver exclusion. Coarse divisor bound forces r=1 in the full sieve at core 589. The test also proves cheap survival together with full-sieve exclusion.

## Checked Lean source SHA-256

```text
e341b766a76a76a4e49d7db7ea69e63defb6c88d88469006b70bd615e740e140  DkMath/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean
99f743b4e04afe5f603e5c6dfb20c3b0cb48067f8613660f0754538f1f7a7893  DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean
```

Full API, failed normalization attempt and fixed-core boundaries: [report-006.md](../report-006.md). Raw transcripts remain disposable in ignored logs. No Git mutation.
