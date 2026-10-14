# FLT7TC-005R18 productionization report

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Source contract: `instruction-023.md`. The implementation was restricted to
the direct `DirectRealCubicRootPacket` route. No successor state, historical
receiver packet, or descent theorem was introduced.

## Implemented production surface

Added `DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitSplit` and exported it
from `DkMath.FLT.Seven`.

The production module now contains:

- `DirectOrbitGapSplit`, using `padicValNat 7` and `divMaxPow` to expose
  `A = 7^k * a`, `0 < a`, and `7 ∤ a`;
- direct gap and homogeneous quotient definitions and their exact product
  factorization from `DirectRealCubicRootPacket`;
- local exact-theta-depth calculus for products, powers, units, integer
  seven-powers, and left-factor cancellation;
- exact quotient depth `3`;
- exact gap depth `32 + 42*k` and the stable corollary
  `eisensteinAxis^32 ∣ directOrbitGap p`;
- current-provenance coprimality of `rho` and `sigma rho`, using the direct
  edge factorization, theta-unit root data, and mapped integer coprimality;
- localization of every common prime of the gap and homogeneous quotient to
  the Eisenstein axis;
- extraction of theta-stripped gap and quotient cores together with their
  current-provenance `IsCoprime` statement.

The extraction of the two stripped cores into explicit unit times seventh
powers, the unit-class equalities, total positivity, and the strict smaller
norm inequality were not added to production in this checkpoint. They remain
the next bounded implementation layer; no unsupported witness or placeholder
axiom was introduced.

## Verification

The following Lean builds were run serially:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitSplit
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitSplitApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitSplitAxiom
```

All four exited successfully. The repository emitted pre-existing warnings
from unrelated research files; the new module emitted only style/linter
warnings. The new axiom audit reports only:

```text
propext, Classical.choice, Quot.sound
```

for each audited theorem. The new source contains no `sorry`, `sorryAx`,
`admit`, `unsafe`, project `axiom`, `CubicGapSeventhShapeReceiver`, or
`RamifiedSignedRootRoutingPacket` input.

The tracked and new-file whitespace checks completed without diagnostics, and
the forbidden-construct scan over the new module and both tests returned no
matches.

## Outcome

**Outcome C — EXACT DEPTH GREEN; STRIPPED CURRENT-PROVENANCE COPRIMALITY IS
GREEN; PID extraction and the Archimedean smaller-norm bridge remain.**

The production frontier is now the explicit associated seventh-power
extraction of the two stripped cores, followed by the real-embedding norm
bound. This checkpoint does not claim a strict descent or unconditional FLT7.
