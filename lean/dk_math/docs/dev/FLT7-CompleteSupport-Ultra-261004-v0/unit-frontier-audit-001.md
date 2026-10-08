# Current normalized carrier: unit and successor frontier audit

- Status: source/applicability audit after `CurrentCarrierNormalizedPower.lean` discharged normalized complete-support divisibility. No additional unit proof campaign was performed in this audit.
- Checked endpoint: `CurrentCarrierPower.currentCarrier_ramified_element_receiver` provides `A = ramifiedUniformizer * u * beta ^ 7`, `IsUnit u`, and the original `Fermat7Equation x y z`. It does not specify the class of this newly extracted unit or construct a successor counterexample.

## Confirmed applicable APIs

- `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero` (`SevenRealCubicUnitClass.lean`) classifies **every real-cubic unit**. It may be applied to `quadraticNormUnit hu.unit`, but proving its projective logarithm is zero remains necessary.
- `projectiveLog_eq_normalized_theta_coords_of_unit_mul_pow_seven` (`PrimeTraceOneDirectRealCubicLocalClass.lean`) is generic in the real-cubic source, unit, and root. It can read the relative-norm unit class from a new norm identity when the current normalized carrier's norm and theta coordinates are supplied.
- `SevenCyclotomicDegreeSixInt.concrete_phase_pow_fourteen` (`PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean`) applies to any degree-six unit: its phase quotient `delta / starUnit delta` has fourteenth power one. This does not imply `delta` itself is a seventh power.
- `SevenCyclotomicDegreeSixInt.relativeNormOneScalarUnitAtSeven_unconditional` is generic: a unit with relative norm one and congruent to one modulo `sevenIdeal` equals one. Both conditions must be proved for the phase of the newly extracted current unit.
- `SevenRealCubic.directOrbit_root_theta_nilpotent_coords_zero` (`PrimeTraceOneDirectRealCubicLocalClass.lean`) already proves `thetaLinearModSeven p.rho = 0` and `thetaSquareModSeven p.rho = 0` from the current gap depth. Thus the scalar-residue input for a future phase-unit calculation is present; no need to assume it.
- Mathlib `IsPrimitiveRoot.geom_sum_isUnit` (`RingTheory/RootsOfUnity/CyclotomicUnits.lean`) proves `S_j = sum i in range j, zeta^i` is a unit for `j.Coprime 7`. It provides a candidate explicit phase gauge for phases 1 through 6.

## Exact carrier and packet mismatch

- Repository search found no Lean declaration named `summitChosenUnitPow` or `currentUnitSector`; the actual relevant declarations are those listed below.
- `DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional` expects a packet with `quotient_eq : directCyclotomicPhaseQuotient r 1 = unit * beta ^ 7`.
- Its source is the original summit endpoint quotient: `directCyclotomicPhaseQuotient r 1 = ofReal (r.summit.endpointRight : SevenRealCubicInt) + directRamifiedGapTail r`. Its raw carrier is `directLinearFactor r = ofReal endpointLeft - zeta * ofReal endpointRight`.
- The new source is `phaseCarrierQuotient p j = zetaInv * ramifiedUniformizer * ofReal (gapAxisQuotient p) + S_j * ofReal p.rho`, with raw carrier `phaseCarrier p j = ofReal (rotateEquiv p.rho) - zeta^j * ofReal p.rho`. These roots are real-cubic elements, not the stored rational summit endpoints. No equality with the original chosen quotient has been proved.
- Therefore the old packet-specific unit theorem cannot be applied by reusing its unit or filling its `quotient_eq` from the new receiver. Doing so would require a new actual source identity, not agreement of scalar norms.
- Existing real-unit sectors `directOrbitPowerSplit_quotientUnit_projectiveLog = (5, 1)` and `directOrbitPowerSplit_gapUnit_projectiveLog = (2, 4)` concern units of a `DirectOrbitPowerSplitPacket p`. The newly extracted degree-six unit is not identified with either of those units or their relative norms.
- Historical `RamifiedSignedRootDepthPacket.elementEquation_coordinate_packet` requires equality with `p.cyclotomicDegreeSixCarrier`; it does not apply to the new `phaseCarrier p j`. The current rho/rotate-rho carrier generally does not lie in the historical two-rational-coordinate slice.

## Candidate next theorem, still unimplemented here

- Phase 1: prove the exact congruence `exists m : Int, not (7 : Int) dvd m and phaseCarrierQuotient p 1 - (m : Ring) in sevenIdeal`. Current gap depth and `directOrbit_root_theta_nilpotent_coords_zero` are candidate inputs. This must be proved for this quotient rather than importing the original endpoint quotient's congruence.
- All nontrivial phases: divide `phaseCarrierQuotient p j` by the explicit cyclotomic unit `S_j`, then establish its rational congruence modulo `(7)`. This phase gauge matters: an arbitrary phase's extracted unit cannot simply be assumed a seventh power.
- A natural stronger target is `exists gamma : Ring, phaseCarrier p j = (1 - zeta^j) * gamma^7` for `0 < j` and `j < 7`. This requires the exact current congruence and the relative-norm/projective-log unit argument. It is a candidate, not a theorem obtained by this audit.
- More directly for a receiver witness `Q_j = u * beta^7`, the next unit obligation is a theorem identifying the class of `u` modulo seventh powers, with the cyclotomic unit `S_j` kept explicit. Generic CM torsion and real-unit classification constrain that class, but the new source calculation has not been connected to them.

## Additive and strict-descent boundary

- `directOrbit_twisted_state_nonempty` and `directOrbit_twisted_state_measure_lt` (`PrimeTraceOneDirectRealCubicSuccessorAudit.lean`) provide a real-cubic twisted seventh-power state with a smaller absolute norm. Its roots are real-cubic and its three coefficients are units; it is not a positive natural-number `CounterexamplePack`.
- The new receiver keeps `source.hEq` for the original `x`, `y`, and `z`. It does not prove an additive Fermat equation for `beta` or construct positive natural successor coordinates.
- Even success of the candidate phase-unit theorem above would require a further landing theorem that produces a new positive primitive counterexample and proves its measure is smaller. No unconditional FLT7 or strict descent follows from the endpoint audited here.

## Next action

- Preserve the proved raw obstruction and corrected complete-support receiver in the main report. Record the new current unit-class calculation and additive successor landing as explicit follow-up obligations; stop this checkpoint without claiming either.
