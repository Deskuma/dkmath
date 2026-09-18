# FLT7TC-005R15 — Explicit CM conjugation transport and torsion phase kill

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the committed R14 state recorded in
`report-019.md`.

The repository now contains the checked algebra equivalence

```lean
SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv :
  (𝓞 (CyclotomicField 7 ℚ)) ≃ₐ[ℤ] SevenCyclotomicDegreeSixInt.Ring
```

and the R13 phase packet

```text
delta = u / starUnit u
quadraticNormUnit delta = 1
delta - 1 ∈ (7).
```

Do not introduce a `Star` instance on the abstract ring of integers.
Current Mathlib already provides explicit CM conjugation APIs.

## Required Mathlib API

Use the explicit CM-field declarations:

```text
NumberField.IsCMField.ringOfIntegersComplexConj
NumberField.IsCMField.unitsComplexConj
NumberField.IsCMField.unitsMulComplexConjInv
NumberField.IsCMField.unitsMulComplexConjInv_apply
IsCyclotomicExtension.Rat.isCMField
IsCyclotomicExtension.Rat.torsionOrder_eq
NumberField.Units.pow_torsionOrder_eq_one
```

For the seventh cyclotomic field, prove/check

```text
torsionOrder (CyclotomicField 7 ℚ) = 14.
```

No reimplementation of Dirichlet/Kronecker theory is needed if these APIs suffice.

## Part A — explicit conjugation coherence

Let

```text
E := ringOfIntegersToRingEquiv
```

and `K := CyclotomicField 7 ℚ`.

Prove that Mathlib's explicit ring-of-integers CM conjugation transports to
the concrete conjugation:

```text
E (ringOfIntegersComplexConj K x)
  = star (E x).
```

Do not rely on a global `Star` instance.

Preferred proof:

1. prove equality of the two ring/algebra homomorphisms;
2. use the integral power basis / generator;
3. show both send the abstract chosen primitive seventh root to
   `zetaInv = zeta^6`;
4. integers are fixed automatically.

If Mathlib exposes the abstract conjugation action on the chosen cyclotomic
root directly, use it. Otherwise derive it from the defining CM conjugation
plus primitive-root uniqueness/order.

Lift the coherence theorem to units:

```text
E_units (unitsComplexConj K U)
  = starUnit (E_units U).
```

Add only the thinnest unit equivalence wrapper required.

## Part B — transport norm-one concrete units to torsion

For an arbitrary concrete unit `delta` satisfying

```text
quadraticNormUnit delta = 1,
```

transport it back through `E` to an abstract unit `Delta`.

Using Part A and the concrete identity

```text
quadraticNormUnit delta = delta * starUnit delta
```

prove

```text
unitsComplexConj K Delta = Delta⁻¹.
```

Then apply

```text
unitsMulComplexConjInv K Delta
```

which is a torsion unit and whose underlying unit is

```text
Delta * (unitsComplexConj K Delta)⁻¹ = Delta^2.
```

Use `torsionOrder = 14` and
`pow_torsionOrder_eq_one` to derive

```text
Delta^28 = 1
```

and transport back:

```lean
delta ^ 28 = 1.
```

A stronger exponent is welcome if proved honestly, but the broad target only
needs 28.

Also calibrate the actual R13 phase. If transporting the original source unit
`u` through `unitsMulComplexConjInv` directly identifies its image with
the phase `u / star(u)`, record whether exponent 14 is available for that
specific packet.

## Part C — purely concrete torsion phase kill modulo (7)

Prove a standalone concrete theorem:

```lean
theorem unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
    (delta : SevenCyclotomicDegreeSixInt.Ringˣ)
    (hpow : delta ^ 28 = 1)
    (hcong :
      ((delta : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal) :
    delta = 1
```

Do not enumerate `± zeta^j` unless that is substantially shorter.

Preferred elementary route:

1. from `hcong`, write `delta = 1 + 7*a`;
2. if `delta ≠ 1`, cancel `delta - 1` from
   `delta^28 - 1 = 0` in the concrete domain to get
   ```text
   S := Σ n in range 28, delta^n = 0;
   ```
3. prove modulo 49:
   ```text
   delta^n ≡ 1 + 7*n*a;
   ```
4. sum from `0` to `27` and use
   ```text
   7 * (0 + ... + 27) ≡ 0 (mod 49)
   ```
   to obtain
   ```text
   S ≡ 28 (mod 49);
   ```
5. `S = 0` would force `28 ∈ (49)`;
6. contradict this using the explicit integral coordinate model of the
   concrete carrier.

Equivalent checked binomial/factorization arguments are acceptable.

Keep this theorem independent of FLT provenance.

## Part D — close RelativeNormOneScalarUnitAtSeven

Combine Parts B and C to prove the existing R13 specification:

```lean
RelativeNormOneScalarUnitAtSeven
```

unconditionally.

Then instantiate the already kernel-checked R13 conditional consequences:

```text
associated unit = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7.
```

Do not rebuild those arguments; reuse the R13 theorems that already encode
the 2/7 Bézout step.

## Part E — bounded downstream audit

After the exact direct factor equation is unconditional, search the existing
clean FLT7 tower for a consumer of

```text
L - zeta*R = (1-zeta) * gamma^7.
```

The consumer must:

- not require the old `CubicGapSeventhShapeReceiver`;
- not depend on `sorryAx`;
- not be circular through an already specialized FLT7 contradiction theorem.

If a clean contradiction follows, prove it.
Otherwise stop at the first exact missing theorem and report it.

## Files

Preferred implementation file:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean
```

Stable carrier-level coherence theorems may live in
`PrimeTraceOneDirectCyclotomicCMUnitPhase.lean` or the PID carrier file if
that is cleaner.

Add focused API and axiom audits.

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-020.md
```

and update `ROADMAP.md`.

## Report questions

1. Was explicit CM conjugation transported through `ringOfIntegersToRingEquiv`?
2. Was unit-level conjugation coherence proved?
3. Was `torsionOrder = 14` checked for the abstract seventh cyclotomic field?
4. For arbitrary norm-one concrete units, was exponent 28 proved?
5. For the actual R13 phase, was exponent 14 available?
6. Was the concrete full-`(7)` torsion phase-kill theorem proved?
7. Was `RelativeNormOneScalarUnitAtSeven` proved unconditionally?
8. Was the actual R12 associated unit proved a seventh power unconditionally?
9. Were `Q₁ = gamma^7` and the direct-factor exact equation made unconditional?
10. Did an existing clean downstream contradiction consumer apply? If not,
    what exact theorem remains first?

## Outcome labels

- **Outcome A — CM TORSION PHASE KILLED; DIRECT CHOSEN QUOTIENT EXACT SEVENTH POWER GREEN.**
- **Outcome B — CM TORSION TRANSPORT GREEN; FULL-(7) PHASE KILL REMAINS.**
- **Outcome C — EXPLICIT CONJUGATION COHERENCE IS THE PRECISE FRONTIER.**
- **Outcome D — AN EARLIER ASSUMPTION ABOUT CM TRANSPORT FAILS.**

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMTorsionPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMTorsionPhaseAxiom
git diff --check
```

Run forbidden-source scans and print axioms for every decisive theorem.
No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

Keep the public facade unchanged unless the exact-power theorem becomes
unconditional and stable.
