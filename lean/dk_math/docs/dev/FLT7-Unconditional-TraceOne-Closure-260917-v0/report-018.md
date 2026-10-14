# FLT7TC-005R13 — Relative-norm-one unit reduction and residual μ₇ phase

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-018.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint starts from
the completed R12 module and remains on the direct
`PrimitiveCounterexampleRamifiedProvenance` route.  It does not use the old
receiver route or a decisive theorem carrying `sorryAx`.

## Implementation

The new module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean`.

It adds:

- `SevenCyclotomicDegreeSixInt.starUnit`, a checked unit-level quadratic
  conjugation map;
- `SevenCyclotomicDegreeSixInt.quadraticNormUnit`, the corresponding unit
  norm map;
- `directRelativeNormOnePhase p = u / starUnit u` for the actual R12 packet
  unit;
- `DirectRelativeNormOnePhasePacket` and its constructor;
- the specification `RelativeNormOneScalarUnitAtSeven` for the remaining
  norm-one unit classification.

For every actual R12 packet, the following are kernel-checked:

```text
quadraticNormUnit (directRelativeNormOnePhase p) = 1
directRelativeNormOnePhase p - 1 ∈ sevenIdeal
```

The congruence is obtained from the R12 unit congruence and the fact that the
packet unit is a unit: the difference `u - star(u)` is in `(7)`, and it is
multiplied by the inverse of the unit-level `star(u)`.  This gives the
stronger congruence to `1`, not just congruence to an unspecified rational
scalar.

The module also proves the exact conditional consequence of killing this
phase.  Assuming `RelativeNormOneScalarUnitAtSeven`, the phase is `1`, hence
`u = star(u)`.  The R12 real norm root then gives `u^2 = t^7`; the explicit
unit-group Bézout calculation with exponents `2` and `7` constructs the root
`t^4 * u⁻¹`.  Consequently the following are available conditionally:

```text
u = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7.
```

## Ten checkpoint questions

1. **Was the preferred phase constructed from the actual R12 unit?** Yes:
   `directRelativeNormOnePhase` uses `p.unit_isUnit.unit` from the actual
   packet.

2. **Was its relative norm proved exactly one?** Yes:
   `directRelativeNormOnePhase_norm_one`.

3. **Was `phase ≡ 1 (mod 7)` proved?** Yes:
   `directRelativeNormOnePhase_sub_one_mem_sevenIdeal`.

4. **Was the ring-of-integers map upgraded to an equivalence?** No.  The
   checked infrastructure still provides only the surjection
   `ringOfIntegersToRing_surjective`.  The exact missing theorem is an
   injectivity/equivalence result for this concrete map; no equal-rank
   surjection-to-isomorphism theorem was found that applies without an
   explicit `1,zeta,...,zeta^5` basis/determinant argument.

5. **Was the relative norm-one unit group classified as torsion or roots of
   unity?** No.  The existing ring-of-integers unit results cannot be
   transported until the concrete map equivalence (or an equivalent direct
   classification) is established.

6. **Were all nontrivial root-of-unity phases killed by the full mod-seven
   congruence?** No classification theorem is available in this concrete
   carrier, so this implication was not asserted.  The phase congruence is
   already at the full ideal `(7)`, not merely at `ramifiedPrime`.

7. **Was `RelativeNormOneScalarUnitAtSeven` proved, even for the actual
   phase?** No.  It remains the first unproved classification target.

8. **Was the original R12 unit proved to be a seventh power?** Only
   conditionally on that target.  The conditional theorem includes the
   checked 2/7 Bézout calculation; no unconditional unit seventh-power claim
   is made.

9. **Were `Q₁ = gamma^7` and the direct factor equation proved?** Only under
   the same phase target.  The unconditional exact-power equations remain
   open.

10. **Does a clean downstream contradiction now exist?** No.  The exact
    frontier is the concrete norm-one phase classification, followed by the
    conditional exact-power equation and a separate no-sorry contradiction or
    descent consumer.  No unconditional FLT7 claim follows here.

## Outcome

**Outcome C — NORM-ONE REDUCTION GREEN; CONCRETE/ABSTRACT UNIT-THEORY
TRANSPORT IS THE PRECISE FRONTIER.**

The preferred unit/star reduction and the full `(7)` congruence are green.
The remaining gap is not a generic “unit normalization” label: it is the
specific theorem `RelativeNormOneScalarUnitAtSeven`, or an equivalent checked
classification of the concrete relative norm-one unit group.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseAxiom
```

The decisive axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The new production and focused audit sources contain no
`sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.  The public facade
was left unchanged because the unconditional phase classification is not yet
a stable theorem surface.
