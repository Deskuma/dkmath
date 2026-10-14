# FLT7TC-005R13 — Relative-norm-one unit reduction and residual μ₇ phase

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the completed R12 module
`PrimeTraceOneDirectCyclotomicUnitCongruence.lean`.
Do not return to the historical receiver route, and do not use any theorem
whose decisive dependency contains `sorryAx`.

## Goal

R12 already provides, for the current counterexample-origin chosen quotient,

```text
Q₁ = unit * beta^7
unit ≡ m (mod 7),  7 ∤ m
quadraticNorm(unit) = realUnit^7
```

with the real-cubic unit class explicitly seventh-power.

Do **not** attack the full degree-six Kummer-unit lemma first.
Reduce it to the smallest relative-norm-one statement.

## Preferred phase: unit / star(unit)

For the actual packet unit `u`, define conceptually

```text
delta := u * (starUnit u)⁻¹
```

where `starUnit` is the unit-level map induced by quadratic conjugation.

Prove:

```text
quadraticNormUnit delta = 1
delta ≡ 1 (mod 7)
```

The second statement should use the R12 congruence
`u ≡ m (mod 7)`, the fact that star fixes rational integers and preserves
`(7)`, and `7 ∤ m` to invert the scalar residue.  This is strictly stronger
than merely saying that `delta` is congruent to some rational scalar.

This phase is preferred over
`u^2 * ofReal(realNormRoot)^(-7)`; use the latter only as a fallback if the
unit-level star/inverse interface is materially harder.

## Required checked interfaces

1. A concrete unit-level quadratic conjugation/star map.
2. A concrete unit-level quadratic norm map, or the thinnest local wrapper.
3. A packet, conceptually:

```lean
structure DirectRelativeNormOnePhasePacket ... where
  sourceUnit : SevenCyclotomicDegreeSixInt.Ringˣ
  phase : SevenCyclotomicDegreeSixInt.Ringˣ
  phase_def : ...
  phase_norm_one : quadraticNormUnit phase = 1
  phase_sub_one_mem_sevenIdeal :
    ((phase : Ring) - 1) ∈ sevenIdeal
```

Keep the actual API minimal and repository-consistent.

## Narrow relative-norm-one target

Introduce only as a specification if not immediately provable:

```lean
def RelativeNormOneScalarUnitAtSeven : Prop :=
  ∀ delta : SevenCyclotomicDegreeSixInt.Ringˣ,
    quadraticNormUnit delta = 1 ->
    ((delta : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal ->
    delta = 1
```

This is intentionally narrower than the full R12
`DegreeSixKummerUnitLemmaAtSeven`.

If this target is proved for the actual phase, obtain

```text
delta = 1
u = star(u)
```

and then use the checked R12 real-norm seventh-power theorem.

If
`quadraticNormUnit u = v^7`
and `u = star(u)`, prove in the degree-six unit group that

```text
u^2 = ofReal(v)^7.
```

Then use Bézout for exponents 2 and 7.  If `u^2 = t^7`, an explicit root is
conceptually

```text
t^4 * u⁻¹
```

because

```text
(t^4 * u⁻¹)^7 = (t^7)^4 * u⁻⁷ = u^8 * u⁻⁷ = u.
```

Kernel-check this group calculation; do not replace it by prose.

This proves the **actual R12 unit** to be a seventh power without first proving
the broad `DegreeSixKummerUnitLemmaAtSeven` for every unit.

## Relative-norm-one classification audit

Attempt `RelativeNormOneScalarUnitAtSeven` by the cheapest honest route.

### Preferred route A — cyclotomic ring of integers

Audit whether the existing surjective map

```text
ringOfIntegersToRing :
  O_(Q(zeta_7)) -> SevenCyclotomicDegreeSixInt.Ring
```

can be upgraded to an equivalence cheaply.

Before building new basis machinery, search Mathlib and existing DkMath for:

- an integral power-basis equivalence already matching the concrete `zeta`;
- a theorem turning a surjective map between these equal-rank torsion-free
  orders into an isomorphism;
- an existing roots-of-unity / CM-unit theorem sufficient for the norm-one
  kernel.

If needed, an explicit `1,zeta,...,zeta^5` basis/determinant proof is allowed,
but do not make it the first choice.

After honest transport to the cyclotomic ring of integers, prove that the
kernel of the CM relative norm on units is torsion / roots of unity.  Do not
assert this directly for the concrete carrier without a checked bridge.

For `Q(zeta_7)`, the expected root-of-unity shape is conceptually
`± zeta^j`; use whatever exact Mathlib formulation is available.

### Preferred route B — direct concrete classification

If substantially shorter, classify only concrete units satisfying
`quadraticNormUnit delta = 1`.
A full classification of all degree-six units is not required.

## Full-mod-seven phase kill

Once a norm-one phase is reduced to a root of unity, use the stronger checked

```text
delta - 1 ∈ (7)
```

to eliminate every nontrivial phase.

Do **not** reduce only modulo `ramifiedPrime`; all `zeta^j` become 1 at that
first ramified level.

The required argument must use the full principal ideal `(7)`, equivalently
the sixth ramified-uniformizer depth, or an explicit coordinate congruence of
the same strength.

Target:

```text
relative norm one
  -> delta is a root of unity
delta ≡ 1 (mod 7)
  -> delta = 1
```

If the available root-of-unity classification includes `-1`, note that
`-1 ≢ 1 (mod 7)`; do not leave a spurious sign branch.

## Consequences if the phase is killed

For the actual R12 packet prove, in order:

```text
unit = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7
```

where all reassociation and unit coercions are explicit.

Then perform a bounded audit: determine whether this exact direct
linear-factor equation feeds an existing no-sorry descent/contradiction
theorem without passing through the old TraceOne receiver.

Do not import a theorem whose conclusion is already FLT7 through a circular
specialized dependency.

## Fallback phase using the real norm root

Only if the preferred `u / star(u)` route is blocked by a genuine missing
unit-level star interface, use the fallback

```text
delta := u^2 * ofReal(v)^(-7)
```

with `quadraticNorm(u)=v^7`.

Then prove norm one and rational-scalar congruence mod `(7)`, classify the
norm-one phase, and show it is a seventh power.  From there derive that
`u^2` is a seventh power and finish with the same Bézout step.

The report must state explicitly why the stronger preferred phase could not be
used.

## Required report questions

Create `report-018.md` and answer:

1. Was the preferred phase `u / star(u)` constructed from the actual R12 unit?
2. Was its relative norm proved exactly one?
3. Was the stronger congruence `phase ≡ 1 (mod 7)` proved?
4. Was the concrete ring-of-integers map upgraded to an equivalence? If not,
   what exact theorem blocks it?
5. Was the relative norm-one unit group classified as torsion/roots of unity?
6. Was every nontrivial root-of-unity phase killed by the full mod-seven
   congruence?
7. Was `RelativeNormOneScalarUnitAtSeven` proved, at least for the actual
   phase packet?
8. Was the original R12 unit proved a seventh power via the checked 2/7 Bézout
   step?
9. Were `Q₁ = gamma^7` and
   `directLinearFactor = ramifiedUniformizer * gamma^7` proved?
10. Does an existing clean downstream theorem now give a contradiction, or
    what exact frontier remains?

## Outcome labels

- **Outcome A — RELATIVE NORM-ONE PHASE KILLED; DIRECT CHOSEN QUOTIENT IS AN EXACT SEVENTH POWER.**
- **Outcome B — NORM-ONE ROOT-OF-UNITY CLASSIFICATION GREEN; FULL MOD-SEVEN PHASE KILL REMAINS.**
- **Outcome C — NORM-ONE REDUCTION GREEN; CONCRETE/ABSTRACT UNIT-THEORY TRANSPORT IS THE PRECISE FRONTIER.**
- **Outcome D — AN EARLIER UNIT-STAR / NORM / CONGRUENCE BRIDGE IS MISSING.**

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseAxiom
git diff --check
```

Run forbidden-source scans for new production/audit files and print axioms for
all decisive new theorems. No `sorry`, `sorryAx`, `admit`, `unsafe`, or
project `axiom` is allowed.

Keep the public `DkMath.FLT.Seven` facade unchanged unless the exact-power
consequences become stable, non-speculative API.
