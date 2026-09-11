# FLT prime-generalization Phase 26 report

## Status

```text
PGEN-PRIME-TRACEONE-CLASSGROUP-CONDITIONAL-GREEN
PGEN-PRIME-TRACEONE-SECTOR-CONDITIONAL-GREEN
PGEN-PRIME-TRACEONE-IMAGINARY-EXACT-POWER-CONDITIONAL-GREEN
PGEN-PRIME-TRACEONE-REAL-FIN-SECTOR-CONDITIONAL-GREEN
```

## Implemented

Added [PrimeTraceOneConditionalDescent.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean), which composes the Phase-25 packet with the existing Phase-16/18 APIs:

- `exists_unit_mul_pow_of_primeTraceOneStrippedIdealPacket` directly applies
  `idealRoot_nonzero` and `residual_span_eq` to the existing class-group
  principalization theorem and retains the explicit unit and generator.
- `exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket` applies the
  neutral `UnitPowerSectorSystem` endpoint without inspecting the sector
  source.
- `exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket` specializes
  the existing singleton imaginary sector theorem for `p >= 7`, `p % 4 = 3`.
- `exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket` specializes
  the existing `Fin p` real sector theorem for `p % 4 = 1`.

The required `TraceOneRat` field, domain, and Dedekind instances are installed
locally in the orchestration endpoints. No global instance or duplicate
principalization/unit-sector proof was added.

## Answers to the required questions

1. Yes. The Phase-25 ideal-root packet composes directly with Phase 16/18:
   `idealRoot_nonzero` and `residual_span_eq` are exactly the inputs required
   by the existing principalization and sector theorems.
2. The strongest branch-independent conditional element statement is
   `residual = u * gamma^p` with `IsUnit u`, together with
   `Ideal.span {gamma} = idealRoot`, under
   `classGroupPTorsionFreeAt R p`.
3. For `p % 4 = 3`, `p >= 7`, and an actual Phase-25 packet, the only new
   arithmetic hypothesis before `residual = delta^p` is exactly
   `classGroupPTorsionFreeAt R p`. The singleton unit-sector result is already
   available; the class-group hypothesis remains conditional and is not proved
   here.
4. For `p % 4 = 1`, the endpoint is exactly
   `residual = rep i * delta^p` for `i : Fin p`, under the same class-group
   hypothesis. No real sector is eliminated.
5. p=3 remains an explicit carrier/API boundary. The existing production
   unit-sector result is stated for `EisensteinInt`, while the generic packet
   uses `TraceOneInt (signedPrimeParameter 3) = TraceOneInt (-1)`. No clean
   production equivalence was present, so no adapter was invented in this
   phase.
6. The remaining mathematical obligations are arbitrary-prime class-group
   `p`-torsion/principalization, real-sector elimination, and—if p=3 is to be
   included in this generic facade—a genuine EisensteinInt/TraceOneInt carrier
   bridge. These are not missing theorem-name or import issues.
7. The generic chain now covers the p-adic split, arbitrary-prime QR/QNR
   TraceOne coordinates, primitive coordinates, discriminant-axis stripping,
   Dedekind ideal extraction, conditional principalization, and neutral sector
   normalization for the supplied odd-prime packet.
8. Before an unconditional FLT contradiction, one still needs the class-group
   hypothesis (or a proof of it), real nonzero-sector elimination, and the
   remaining FLT-side contradiction/receiver. The p=3 carrier boundary must
   also be resolved if that exponent is included.

## p=3 and finite regressions

[PrimeTraceOneConditionalDescentApiAudit.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMathTest/FLT/Prime/PrimeTraceOneConditionalDescentApiAudit.lean)
records the exact packet, principalization, sector, branch, and Phase-17
instance signatures, including the p=3 Eisenstein carrier API.

[PrimeTraceOneConditionalDescentProbe.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMathTest/FLT/Prime/PrimeTraceOneConditionalDescentProbe.lean)
checks the conditional architecture at p=5, 7, 11, and 13 using actual
Phase-25 packets. It also audits the existing p=3 Eisenstein sector theorem
and compares p=7 with `SevenQuadraticResidualPacket.norm_is_seventh_power`.

## Validation and audits

The requested focused targets built successfully:

```text
DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector
DkMath.NumberTheory.TraceOnePrimeUnitSectors
DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentApiAudit
DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentProbe
DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentAxiomAudit
DkMath.FLT.Seven
```

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
for all new public conditional endpoints. The Phase-26 production and test
source scan found no `sorry`, `sorryAx`, `admit`, explicit `axiom`, or
`unsafe`. `git diff --check` passed.

The focused build also replays the pre-existing warning in
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`; that declaration
is outside Phase 26 and was not modified or attributed to this phase.
