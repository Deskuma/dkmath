# FLT7TC-005R14 — Concrete cyclotomic CM transport and norm-one phase kill

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the completed R13 module
`PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean`.

The first unproved theorem is exactly

```lean
RelativeNormOneScalarUnitAtSeven
```

Do not return to the historical TraceOne receiver/reconstruction route.
Do not use a theorem whose decisive dependency contains `sorryAx`.

## New Mathlib surface to use

Mathlib already contains the CM-field theorem

```text
NumberField.IsCMField.unitsMulComplexConjInv :
  (O K)ˣ ->* NumberField.Units.torsion K
```

whose value is `u * (complexConj u)⁻¹`.

For a seventh cyclotomic field, Mathlib also contains

```text
IsCyclotomicExtension.Rat.isCMField
IsCyclotomicExtension.Rat.torsionOrder_eq
NumberField.Units.pow_torsionOrder_eq_one
```

and `torsionOrder = 14` for `n = 7`.

Exploit these existing theorems.  Do not re-prove Dirichlet or Kronecker
theory if the CM API suffices.

## Primary goal

Upgrade the existing concrete/abstract map

```lean
SevenCyclotomicDegreeSixInt.ringOfIntegersToRing :
  (O (CyclotomicField 7 Q)) ->ₐ[Z] SevenCyclotomicDegreeSixInt.Ring
```

from its already checked surjectivity to an honest equivalence, then transport
the R13 relative-norm-one phase through Mathlib's CM-unit torsion theorem.

The desired final result of this checkpoint is an unconditional proof of

```lean
RelativeNormOneScalarUnitAtSeven
```

and therefore, by the already checked R13 consequences, the actual
counterexample-origin equations

```text
R12 associated unit = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7.
```

## Part A — make the concrete carrier the cyclotomic ring of integers

### A1. Prove injectivity of the existing map

Add, preferably near the existing PID transport:

```lean
theorem ringOfIntegersToRing_injective :
  Function.Injective ringOfIntegersToRing
```

and then a ring/algebra equivalence, conceptually

```lean
noncomputable def ringOfIntegersEquivRing :
  (O (CyclotomicField 7 Q)) ≃+* Ring
```

or an `AlgEquiv Z` if that is more convenient.

The existing source map is built from the integral power basis and sends the
chosen abstract primitive seventh root to the concrete `zeta`.

### A2. Preferred injectivity proof

Do **not** begin with a large new number-field construction.

The concrete carrier already has

```text
coordinates : Ring ≃+ (Fin 6 -> Z)
rankOverIntegers_eq_six
```

and the abstract ring of integers already has the cyclotomic integral
power basis of dimension six.

Prefer a finite-rank / explicit power-basis argument:

- express an abstract integer in the integral power basis;
- map the six coefficients to
  `1, zeta, ..., zeta^5`;
- use the concrete six coordinates to prove these six vectors are
  `Z`-linearly independent (or directly form a unimodular basis);
- conclude the kernel is zero.

A small explicit 6-by-6 determinant computation is acceptable.
Use `fin_cases`, concrete coordinates and `norm_num`/ring normalization
rather than introducing a broad generic matrix framework unless it is
actually shorter.

Before doing this, search the current Mathlib/DkMath APIs for a direct theorem
that makes the surjective equal-rank map injective.

### A3. Star / complex-conjugation coherence

Once the equivalence exists, prove that it intertwines:

```text
Mathlib CM complex conjugation
    <->
SevenCyclotomicDegreeSixInt.star
```

on ring elements and units.

It is enough to prove equality of the two ring homomorphisms on the integral
power-basis generator / primitive seventh root and on integers.

The concrete facts already include

```text
star zeta = zetaInv
zetaInv = zeta^6
zeta^7 = 1.
```

Use Mathlib's CM/cyclotomic conjugation theorem on the abstract root where
possible.

## Part B — transport relative norm-one units to torsion

Let `delta : Ringˣ` satisfy

```text
quadraticNormUnit delta = 1.
```

Transport it to an abstract unit `Delta : (O K)ˣ`, where
`K = CyclotomicField 7 Q`.

Using star/complex-conjugation coherence, prove

```text
complexConj(Delta) = Delta⁻¹.
```

Then Mathlib's

```text
unitsMulComplexConjInv K Delta
```

is the torsion unit represented by

```text
Delta / complexConj(Delta) = Delta^2.
```

For the seventh cyclotomic field,

```text
torsionOrder K = 14.
```

Therefore derive

```text
Delta^28 = 1
```

and transport this back to

```lean
delta ^ 28 = 1
```

in the concrete unit group.

A stronger exponent is allowed if obtained naturally, but do not assume
`delta^14 = 1` unless it is actually proved.

For the actual R13 phase `u / star(u)`, a direct transport through
`unitsMulComplexConjInv` may give exponent 14.  This is a useful calibration,
but the broad `RelativeNormOneScalarUnitAtSeven` target should preferably be
proved from the norm-one hypothesis itself.

## Part C — kill a torsion unit congruent to 1 modulo (7)

Prove a purely concrete lemma, conceptually:

```lean
theorem unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
    (delta : Ringˣ)
    (hpow : delta ^ 28 = 1)
    (hcong : ((delta : Ring) - 1) ∈ sevenIdeal) :
    delta = 1
```

Do not enumerate roots of unity unless this is genuinely shorter.

### Preferred elementary proof

From `hcong`, obtain

```text
delta = 1 + 7*a
```

for some concrete carrier element `a`.

Use the factorization

```text
delta^28 - 1 = (delta - 1) * (1 + delta + ... + delta^27).
```

If `delta ≠ 1`, domain cancellation gives

```text
S := 1 + delta + ... + delta^27 = 0.
```

Prove the first-order congruence modulo 49

```text
delta^n ≡ 1 + 7*n*a  (mod 49)
```

by induction on `n`.
Summing `n = 0,...,27` yields

```text
S ≡ 28 (mod 49)
```

because

```text
7 * sum_{n=0}^{27} n
```

is divisible by 49.

Thus `S = 0` would imply that the integer `28` lies in the principal ideal
`(49)` of the concrete carrier.

Close that impossibility using the explicit integral coordinate model
(e.g. the first coordinate would give `28 = 49*k` in `Z`).
An equivalent checked argument is fine.

A direct binomial factorization
`(1+7a)^28 - 1 = 49*a*(4 + 7*b)`
is also acceptable if Lean handles it cleanly.

## Part D — close the R13 specification

Combine Parts B and C to prove

```lean
theorem relativeNormOneScalarUnitAtSeven :
  RelativeNormOneScalarUnitAtSeven
```

or replace the specification by a proved theorem if repository style prefers.

Then instantiate the already checked R13 conditional results to prove
unconditionally for every actual R12 packet:

```text
associated unit = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7.
```

Do not silently replace the stored PID-selected packet unit by another
associated unit.

## Part E — bounded downstream audit

Only after the exact direct factor equation is unconditional, perform a
bounded search for an existing clean consumer of

```text
L - zeta*R = (1-zeta) * gamma^7.
```

Possible historical consumers may live in the ramified cyclotomic / additive
chart / descent tower.

The audit must answer whether a current no-`sorryAx` theorem can consume this
equation **without** requiring the old TraceOne receiver or a circular FLT7
closure theorem.

Do not force a contradiction in this checkpoint if no clean consumer exists.

## Alternative if the ring equivalence is genuinely expensive

Before stopping, audit one fallback only:

- construct the fraction field / number field of the concrete PID carrier;
- use the concrete star as CM conjugation;
- apply Mathlib's Kronecker/CM unit theory there.

Use this only if it is demonstrably shorter than proving
`ringOfIntegersToRing_injective`.

Do not start a second large algebraic infrastructure in parallel.

## Files

Preferred new production file:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMUnitPhase.lean
```

If injectivity/equivalence belongs naturally in
`SevenRamifiedFusionCyclotomicDegreeSixPID.lean`, add only the stable
carrier-level theorem(s) there and keep the FLT7 specialization in the new
module.

Add focused API and axiom audits.

Create `report-019.md` and update `ROADMAP.md`.

## Report questions

1. Was `ringOfIntegersToRing_injective` proved?
2. Was a concrete ring-of-integers equivalence constructed?
3. Was concrete star proved coherent with Mathlib CM complex conjugation?
4. Was the concrete relative norm-one unit transported to Mathlib torsion?
5. What exact torsion exponent was obtained: 14, 28, or another checked value?
6. Was the purely concrete full-`(7)` torsion phase-kill lemma proved?
7. Was `RelativeNormOneScalarUnitAtSeven` proved unconditionally?
8. Was the R12 associated unit proved a seventh power unconditionally?
9. Were `Q₁ = gamma^7` and
   `directLinearFactor = ramifiedUniformizer * gamma^7` made unconditional?
10. Does a clean existing downstream contradiction/descent consumer now apply?
    If not, state the exact first missing theorem.

## Outcome labels

- **Outcome A — CM UNIT PHASE KILLED; DIRECT CHOSEN QUOTIENT EXACT SEVENTH POWER GREEN.**
- **Outcome B — CONCRETE/ABSTRACT EQUIVALENCE AND CM TORSION TRANSPORT GREEN; FULL-(7) TORSION PHASE KILL REMAINS.**
- **Outcome C — INJECTIVITY / RING-OF-INTEGERS EQUIVALENCE IS THE PRECISE FRONTIER.**
- **Outcome D — AN EARLIER STAR/CM TRANSPORT ASSUMPTION FAILS.**

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMUnitPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMUnitPhaseAxiom
git diff --check
```

If `SevenRamifiedFusionCyclotomicDegreeSixPID.lean` changes, also run its
focused build / existing axiom audit surfaces.

Run forbidden-source scans for every new or modified decisive source.
No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

Keep the public `DkMath.FLT.Seven` facade unchanged unless the phase target
and exact-power consequences are fully unconditional and judged stable.
