# FLT prime-generalization Phase 16 — principal ideal to element-power bridge

## Goal

Close the remaining neutral bridge between the Phase-15 ideal/class-group route and the Phase-14 element/unit route.

The mathematical chain to formalize is:

```text
span(a) = I^p
I ≠ 0
classGroupPTorsionFreeAt R p
        |
        v
I is principal
        |
        v
I = span(gamma)
        |
        v
span(a) = span(gamma^p)
        |
        v
a ~ gamma^p
        |
        +-- retain the unit explicitly: a = u * gamma^p
        |
        +-- if p-th power is surjective on R^×: a = delta^p
```

This phase must remain neutral: no FLT, no Kummer receiver, no fixed prime, no TraceOne specialization.

## Existing code to audit first

Before implementing, inspect the pinned signatures and reuse the strongest existing Mathlib route.

Relevant existing DkMath specializations:

- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID.unitMulPowOfSpanEqPow`
- `DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower.exists_mul_pow_of_span_eq_mul_pow`
- the generator/unit lemmas already present in `DkMath.FLT.Kummer.CyclotomicPrincipalization`

Relevant Mathlib declarations include at least:

```text
Ideal.span_singleton_eq_span_singleton
Ideal.span_singleton_pow
Ideal.span_singleton_mul_span_singleton
Ideal.span_singleton_mul_left_unit
Submodule.IsPrincipal.generator
Submodule.IsPrincipal.span_singleton_generator
```

Do not duplicate a ready-made theorem if the pinned checkout already supplies the exact neutral statement.

## Part A — generic principal-generator bridge

Add a neutral production module, preferably:

```text
DkMath/Lib/NumberTheory/PrincipalIdealPower.lean
```

with only neutral imports (`Mathlib` plus the Phase-14/15 neutral modules if useful).

First expose the smallest reusable bridge from equality of principal ideals to association, for example:

```lean
theorem associated_of_span_singleton_eq_span_singleton
    {R : Type*} [CommRing R] [IsDomain R]
    {a b : R}
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    Associated a b
```

If this is exactly a Mathlib theorem, use a thin wrapper or skip the duplicate and document the pinned declaration.

## Part B — local principality, no global PID assumption

The main bridge should require only that the particular ideal is principal, not `[IsPrincipalIdealRing R]` globally.

Target shape:

```lean
theorem exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI : I.IsPrincipal)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧
      Ideal.span ({gamma} : Set R) = I ∧
      a = u * gamma ^ p
```

Equivalent signatures are acceptable if they preserve the same mathematical content and avoid a global PID assumption.

If `I.IsPrincipal` does not expose a convenient local generator in the pinned API, audit the exact representation first; do not silently strengthen to `IsPrincipalIdealRing` unless unavoidable. If a stronger assumption is required, report it explicitly.

Also expose the associated form if it simplifies composition:

```lean
∃ gamma, Ideal.span ({gamma} : Set R) = I ∧ Associated a (gamma ^ p)
```

## Part C — compose with Phase 15 principalization

Using `classGroupPTorsionFreeAt` and
`ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt`, prove the conditional ideal-to-element endpoint.

Preferred theorem shape:

```lean
theorem exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧
      Ideal.span ({gamma} : Set R) = I ∧
      a = u * gamma ^ p
```

Reason:

- `hspan` makes `I^p` principal;
- Phase 15 principalizes `I`;
- Part B converts principal-ideal equality to an element equation with an explicit unit.

No class-number theorem or regular-prime theorem is to be introduced.

## Part D — merge with the Phase-14 unit-sector API

Reuse

```text
DkMath.Lib.NumberTheory.eq_pow_of_associated_pow_of_unit_pow_surjective
```

or an equivalent neutral helper to prove the final conditional exact-power theorem:

```lean
theorem exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ delta : R, a = delta ^ p
```

Equivalent theorem names/signatures are acceptable, but the unit hypothesis must remain explicit. Do not claim it for arbitrary quadratic orders.

## Part E — relation between the two routes

Add a short audit/probe documenting that the two neutral routes now converge at exactly the same unit-sector frontier:

```text
Element route:
  x*y = z^p + coprime
    -> Associated x (gamma^p)
    -> exact p-th power only with unit p-surjectivity

Ideal route:
  span(a) = I^p
  + class-group p-torsion-free
    -> I principal
    -> Associated a (gamma^p)
    -> exact p-th power only with unit p-surjectivity
```

The purpose is to make it impossible for later FLT code to hide the unit obligation inside principalization.

## Part F — finite compatibility audit

Probe the generic bridge on the already available arithmetic carriers where instances exist:

- p=3 / `TraceOneInt (-1)`
- p=7 / `TraceOneInt (-2)`
- p=5 / `GoldenInt` only if the required carrier instances synthesize cleanly

Do not infer anything for `TraceOneInt 1`, `TraceOneInt (-3)`, or `TraceOneInt 3` merely from the Phase-13 norm bridge.

For p=7, compare the neutral output with the existing specialized `unitMulPowOfSpanEqPow` / seventh-power extraction route. Compatibility is enough; do not rewrite the FLT7 tower in this phase.

## Part G — classification

If Part B and Part C succeed, report:

```text
PGEN-PRINCIPAL-IDEAL-ELEMENT-BRIDGE-GREEN
```

If Part D also succeeds, additionally report:

```text
PGEN-IDEAL-TO-EXACT-POWER-CONDITIONAL-GREEN
```

The word `CONDITIONAL` is important: class-group p-torsion-freeness and unit p-surjectivity remain assumptions.

Do not report a general FLT theorem, a regular-prime theorem, class-group vanishing, or arbitrary unit absorption.

## Verification

Add test-first probe and axiom-audit modules under:

```text
DkMathTest/FLT/Prime/
```

At minimum build:

```text
lake build DkMath.Lib.NumberTheory.PowerFactor
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMath.Lib.NumberTheory.PrincipalIdealPower
<new probe>
<new axiom audit>
lake build DkMath.FLT.Seven
```

Run:

```text
git diff --check
```

and scan new Phase-16 sources for `sorry`, `sorryAx`, and explicit `axiom`.

## Report

Write:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-016.md
```

The report must distinguish clearly:

1. principal-ideal equality -> Associated / unit-times-power;
2. class-group p-torsion-free -> principality;
3. unit p-surjectivity -> exact p-th power;
4. which of these are proved generically and which remain carrier-specific assumptions.
