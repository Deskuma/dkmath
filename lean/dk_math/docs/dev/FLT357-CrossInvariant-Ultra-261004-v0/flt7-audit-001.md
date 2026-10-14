# Current FLT7 source projection — FLT357 pre-audit

2026-10-04. Source audit on the live branch, not a new proof campaign.

## Exact production layers

| Axis | Current source and mathematical scope |
| --- | --- |
| Original integer/GN | `Seven.CounterexampleRouting.Body7 g y = g * GN 7 g y`; `body7_eq_seventh_power_of_counterexample` retains the original Fermat equality. `counterexampleRoute_of_pack` distinguishes a coprime away split from `SevenAdicCounterexamplePacket`. |
| Source carrier and generation | `DirectRealCubicRootPacket` (`PrimeTraceOneDirectRealCubicOrbit`) contains an already extracted cyclotomic root, its **relative quadratic norm** `rho`, `directChosenQuotientRealSource r = rho^7`, and the residual integer norm. The later current `A_j=ofReal(rotate rho)-zeta^j*ofReal rho` is a root-orbit carrier, not the original rational-endpoint cyclotomic factor. |
| Actual order | `SevenCyclotomicDegreeSixInt.Ring` is an explicit quadratic algebra over the real cubic order `SevenRealCubicInt`. Its checked degree-six cyclotomic/ring-of-integers equivalence and PID instance come from `SevenRamifiedFusionCyclotomicDegreeSixPID`. It is not `TraceOneInt (-2)`. |
| Ramifier | `ramifiedUniformizer=1-zeta`, `ramifiedPrime=ker ramifiedEval`, and `ramifiedPrime_eq_span_uniformizer` (`SevenRamifiedFusionCyclotomicRamifiedPrime`). `CurrentCarrierRamification` proves actual element division and quotient residue; current A is in P7 but not P7². |
| Full normalized ideal power | `CurrentCarrierPower.normalizedPhaseIdeals_pairwise`, the complete six-factor product, and the current `axis^3*U*S^14` decomposition give `normalizedPhaseIdeal_seventh_power` for every phase j=1..6. `normalized_completeSupport_seventh_divisibility` covers all height-one support, not one selected address. |
| Element receiver | `currentCarrier_ramifiedIdeal_mul_seventh_power`: `(A)=P7*J^7`; `currentCarrier_ramified_element_receiver`: `A=lambda*u*beta^7`, `IsUnit u`, original `Fermat7Equation x y z`. No extra exponent or class-group premise; existing PID provides principalization. Current counterexample/root/common-factor/address inputs are still required. |
| Full raw exponents | `CurrentAggregation.ramifiedPlace_exponent` is 1; `away_ramified_exponent_seventh_dvd` covers every other prime. `not_completeSupport_seventh_divisibility` negates the raw-target condition under the same packet inputs. |
| Unit / phase | The new degree-six u is retained. `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero` gives an exact criterion for **real-cubic** units, using two `ZMod 7` projective coordinates. `unit_rank_eq_two` and `unitClassProjectiveLog_bijective` concern that real cubic unit group. They do not identify the new full-degree-six unit with a real one. |
| Integral/additive landing | Exact `currentLinearCarrier_eq_phaseCarrier` and exact lambda division retain element identity, while the receiver retains original `source.hEq`. Neither gives a Fermat equation for natural coordinates of beta. Historical two-rational-coordinate packets cannot be substituted for rho/rotate-rho coordinates. |
| Descent | `directOrbit_twisted_state_measure_lt` (`PrimeTraceOneDirectRealCubicSuccessorAudit`) supplies a smaller **twisted real-cubic state norm**. It does not reconstruct a positive natural `CounterexamplePack`, nor a recursive current ramified packet with strict natural decrease. |

## Honest reverse projection

```text
current raw root-orbit phase factor
 -> one lambda, exact ramified exponent1
 -> all six normalized phase ideals pairwise coprime, complete product power
 -> normalized ideal seventh power
 -> checked PID: normalized element = u*beta^7
 -> new u class / integral additive successor unresolved
```

The common extracted form with p=3 and p=5 is real: each selected production
stage has a chosen actual order/ramifier and a nonzero raw element equal to
ramifier * unit * p-th power. This does not identify the source elements or
orders across exponents, or make their coordinate descent algorithms equal.

## Carrier-specific unit boundary

`DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional`
(`PrimeTraceOneDirectCyclotomicCMTorsionPhase`) concerns
`directCyclotomicPhaseQuotient r 1`, the original summit rational-endpoint
quotient. It is a different source from the newly divided `phaseCarrierQuotient
p j`. No equality transfers that packet's unit theorem to the new u.

CM phase/relative-norm unit APIs apply to arbitrary degree-six units only when
their separate scalar congruence and relative-norm conditions are proved. The
current root's nilpotent coordinates vanish modulo 7; a new quotient/phase-gauge
calculation must connect those facts to this extracted unit. No such bridge is
proved by this pre-audit.

The generic signed-quadratic route at p=7 has exact residual powers in
`TraceOneInt (-2)` and sign-only units. That does not remove a degree-six unit:
the former is the imaginary quadratic Gauss/QR companion, while the latter
comes from the full cyclotomic order over a real-cubic source. DRC-007 offers an
actual quadratic embedding and QR product identity, but not identity with this
single root-orbit factor.

## Earliest genuine split from the low-degree routes

At carrier generation, p=3 uses a linear Eisenstein norm, p=5 a square-linked
Golden binary norm with retained discriminant-square source, and current p=7
an already extracted real-cubic root followed by a degree-six orbit factor.
This is mathematical arithmetic/provenance, not a namespace choice. The honest
common invariant can therefore compare their **extracted power obstruction**;
it cannot silently turn them into one literal signed-quadratic FLT proof.

No production source was edited and no new FLT7 theorem was requested here.
Focused endpoint/axiom/provenance checks are recorded centrally in the findings
and validation log.
