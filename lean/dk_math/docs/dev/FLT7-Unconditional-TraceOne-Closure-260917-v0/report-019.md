# FLT7TC-005R14 — Cyclotomic ring-of-integers equivalence for the CM phase

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-019.md` was treated as the bounded implementation
contract, separately from the user's request. This checkpoint starts from R13
and does not use the historical receiver route or any declaration carrying
`sorryAx`.

## Implementation

The new module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMUnitPhase.lean`.

The PID layer now proves
`SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_injective`. The proof is
explicit and kernel-checked:

- the concrete carrier has characteristic zero via its first coordinate;
- the carrier generator has minimal polynomial `cyclotomic 7 ℤ`, by passing
  to the fraction field and using the primitive-root minimal-polynomial result;
- `PowerBasis.equivOfMinpoly` identifies the concrete integral power basis
  with the existing cyclotomic ring-of-integers power basis;
- the existing power-basis map is therefore injective.

Together with the existing surjectivity theorem this gives the public algebra
equivalence `ringOfIntegersToRingEquiv` and checked injective/surjective
projections.

The source ring-of-integers type has no `Star` instance in the current
Mathlib surface, so no artificial star instance or unproved CM coherence was
introduced. The abstract-to-concrete star transport and the subsequent
relative norm-one classification remain explicit next targets.

## Bounded status

Part A is green: the concrete ring-of-integers map is now an equivalence.
R13's actual phase construction, norm-one identity, and `(7)` congruence remain
available unchanged. Parts B–D are not claimed: the CM unit torsion transport,
the concrete mod-49 phase kill, and the unconditional seventh-power closure
still require a checked source CM involution/classification bridge.

## Outcome

**Outcome C — RING-OF-INTEGERS EQUIVALENCE GREEN; CM STAR/TORSION TRANSPORT IS
THE PRECISE FRONTIER.**

No unconditional `Q₁ = gamma^7`, direct-factor seventh-power equation,
contradiction, receiver, or FLT7 conclusion follows from this checkpoint.

## Validation

The focused production builds completed successfully:

```text
lake build DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMUnitPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMUnitPhaseAxiom
```

The corresponding API and axiom audit files were added under `DkMathTest/FLT`,
and the public `DkMath.FLT.Seven` facade remains green. `git diff --check` and
the no-forbidden-construct scan are clean. The R13 focused builds remain green.
The production/API/Axiom sources for this checkpoint contain no `sorry`,
`sorryAx`, `admit`, `unsafe`, or project `axiom`.
