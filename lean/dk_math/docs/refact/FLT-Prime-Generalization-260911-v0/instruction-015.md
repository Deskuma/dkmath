# FLT prime-generalization Phase 15 — ideal/class-group arithmetic kernel

## Goal

Phase 14 isolated the first genuinely arithmetic frontier after the arbitrary-prime
TraceOne front-end:

```text
coprime element factors of a p-th power
  -> associated p-th powers                    [GENERIC, GREEN]
  -> exact p-th powers                         [UNIT-SECTOR]

non-UFD / non-GCD route:
principal element equation
  -> coprime ideal factors
  -> ideal p-th power
  -> class-group p-torsion
  -> principalization
  -> unit-sector normalization
```

Phase 15 should formalize only the **neutral ideal/class-group kernel** of the
second route. Do not attempt a general FLT theorem, a general TraceOne
Dedekind-domain instance, a class-number theorem, a regular-prime theorem, or a
unit classification.

The main question is:

> Once an ideal class has p-th power equal to 1, can DkMath expose a small,
> reusable theorem saying that p-torsion-freeness of the class group forces
> principalization, independently of FLT/Kummer receiver targets?

A secondary question is whether the coprime ideal-factor extraction itself can
be expressed by existing UFD/GCD/normalized-factor APIs without introducing a
new bespoke ideal factorization proof.

## Architectural rule

Do **not** import `DkMath.FLT.*` from the neutral production module.

Existing Kummer files such as:

```text
DkMath.FLT.Kummer.ClassGroupBridge
DkMath.FLT.Kummer.CyclotomicPrincipalization
```

are audit/comparison sources only. Their FLT receiver types and historical
conditional routes must not become dependencies of the new generic kernel.

Prefer a production location such as:

```text
DkMath/Lib/NumberTheory/IdealPowerFactor.lean
```

or, if the class-group material is cleaner separately:

```text
DkMath/Lib/NumberTheory/IdealPowerFactor.lean
DkMath/Lib/NumberTheory/ClassGroupPTorsion.lean
```

## Part A — pinned Mathlib audit

Inspect the pinned checkout and record exact usable declarations for:

- Dedekind-domain ideal unique factorization;
- normalized ideal factors / multiplicities;
- principal ideals and principal generators;
- `ClassGroup.mk0` / `ClassGroup.mk` and the theorem characterizing class 1;
- multiplication/powers in the class group;
- passage from ideal powers to class-group powers;
- any existing theorem of the form “if the class of `I` is 1 then `I` is
  principal”.

At minimum audit the families already identified in Phase 14:

```text
Ideal.uniqueFactorizationMonoid
Ideal.prod_normalizedFactors_eq_self
Ideal.count_normalizedFactors_eq_multiplicity
FractionalIdeal.finprod_heightOneSpectrum_factorization
FractionalIdeal.finprod_heightOneSpectrum_factorization_principal
ClassGroup.mk0
ClassGroup.mk0_eq_one_iff
ClassGroup.mk0_eq_mk0_iff
ClassGroup.mk0_surjective
ClassGroup.mk_eq_one_iff
Submodule.IsPrincipal.generator
```

Do not assume the exact signatures from memory; use the pinned source.

## Part B — neutral p-torsion-free predicate

If no suitable existing predicate is already available, introduce a very thin
neutral definition, preferably in `DkMath.Lib.NumberTheory`:

```lean
classGroupPTorsionFreeAt (R : Type*) (p : ℕ) : Prop :=
  ∀ a : ClassGroup R, a ^ p = 1 -> a = 1
```

Use the weakest actual typeclass assumptions required by `ClassGroup R` in the
pinned Mathlib. Do not overstate Dedekind/PID/UFD hypotheses if the declaration
itself needs less.

If a pre-existing Mathlib predicate expresses exactly this property, prefer it
and add only a DkMath wrapper if that materially improves API stability.

## Part C — principalization from class-group p-torsion

Target a theorem morally equivalent to:

```lean
principal_of_pow_class_trivial
```

or

```lean
isPrincipal_of_classGroup_p_torsion_free
```

with content:

- `I` is a nonzero (fractional or integral, whichever pinned API makes honest)
  ideal;
- the class `[I]` satisfies `[I]^p = 1`;
- the class group is p-torsion-free;
- therefore `I` is principal.

A stronger but still acceptable endpoint is:

```text
I^p principal
  + classGroupPTorsionFreeAt R p
  -> I principal
```

provided the passage `I^p principal -> [I]^p = 1` is proved in the same
neutral module.

Important: preserve the distinction

```text
ideal principalization
```

from

```text
element = unit * p-th power
```

The latter still requires a generator comparison and then a separate
unit-sector theorem. Phase 15 must not hide unit absorption inside the
class-group theorem.

## Part D — coprime ideal p-th-power extraction probe

Test whether the following can be obtained from existing generic factorization
machinery with a small wrapper:

```text
I * J = K^p
coprime(I,J)
----------------
∃ A, I = A^p
```

(and symmetrically for `J`).

Possible routes to audit:

1. instantiate the Phase-14 generic associated-power theorem on an ideal-like
   GCD/UFD carrier if the required instances exist;
2. use `Ideal.uniqueFactorizationMonoid` / normalized factors directly;
3. use fractional ideals if integral ideals make units/zero awkward.

Do not force a theorem if the pinned typeclass/API boundary is hostile. If the
clean result naturally lives for nonzero fractional ideals, report that and
use that carrier.

The theorem should be classified separately from principalization:

```text
ideal factor extraction      [unique-factorization layer]
principalization             [class-group layer]
unit absorption              [unit-sector layer]
```

## Part E — relation to the element-level Phase-14 API

Add a small test/probe explaining how the two routes compare:

```text
GCD/UFD element route:
  x*y=z^p + gcd=1
    -> x ~ gamma^p
    -> exact equality only after unit p-surjectivity

Dedekind ideal route:
  (x)(y)=(z)^p + coprime ideals
    -> (x)=A^p
    -> class[A]^p=1
    -> A principal under p-torsion-free class group
    -> x = unit * gamma^p
    -> exact equality only after unit p-surjectivity / sector control
```

This comparison is documentation/test-side only unless a genuinely reusable
bridge theorem falls out cheaply.

## Part F — finite specialization audit

Do not prove new arithmetic for `TraceOneInt(s_p)` merely to populate a table.
Instead record which Phase-13 samples can currently instantiate the ideal route
with **proved** ring arithmetic:

```text
p=3, s=-1
p=5, s=1
p=7, s=-2
p=11, s=-3
p=13, s=3
```

Be strict about carrier mismatch:

- FLT5 GoldenInt results do not automatically instantiate `TraceOneInt 1`;
- an existing Euclidean `TraceOneInt(-1)` or `TraceOneInt(-2)` result may imply
  PID/Dedekind consequences through Mathlib, but only count them if the
  necessary instances actually synthesize in the pinned checkout;
- no arithmetic conclusion for p=11/13 should be inferred from the Phase-13
  norm bridge alone.

## Part G — classification

Use one of the following as the highest achieved classification:

```text
PGEN-IDEAL-FACTOR-GREEN
  coprime ideal factors of a p-th power are extracted as ideal p-th powers

PGEN-CLASSGROUP-PRINCIPALIZATION-GREEN
  class-group p-torsion-free hypothesis yields principalization of the
  extracted p-th root ideal

PGEN-IDEAL-ARITHMETIC-API-READY
  pinned APIs are identified but a clean neutral theorem is blocked

PGEN-IDEAL-ARITHMETIC-BOUNDARY
  the desired statement is false or requires materially stronger hypotheses
```

If both factor extraction and principalization are green, report both and use
`PGEN-CLASSGROUP-PRINCIPALIZATION-GREEN` as the phase headline.

## Part H — test-first and trust checks

Add focused tests, suggested names:

```text
DkMathTest/FLT/Prime/IdealPowerFactorAuditProbe.lean
DkMathTest/FLT/Prime/IdealPowerFactorAuditAxiomAudit.lean
```

If production is split into two modules, audit both.

Required checks:

```text
lake build DkMath.Lib.NumberTheory.PowerFactor
lake build <new neutral ideal/class-group module(s)>
lake build DkMathTest.FLT.Prime.IdealPowerFactorAuditProbe
lake build DkMathTest.FLT.Prime.IdealPowerFactorAuditAxiomAudit
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.FLT.Seven
```

Also run:

```text
#print axioms
```

for every new public theorem, scan changed production/test files for new
`sorry`, `sorryAx`, or explicit `axiom`, and run `git diff --check`.

## Part I — report

Write:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-015.md
```

The report must answer:

1. What is the weakest clean carrier for coprime ideal p-th-power extraction?
2. Is ideal factor extraction already available from pinned generic UFD/GCD
   machinery, or did a new factorization proof have to be written?
3. What exact theorem converts class-group p-torsion-freeness into
   principalization?
4. Is `I^p principal -> [I]^p = 1` formalized cleanly?
5. After principalization, what remains before obtaining an exact element
   p-th power? Explicitly separate generator/unit comparison from unit-sector
   absorption.
6. Which of p=3,5,7,11,13 can actually instantiate the required arithmetic
   assumptions today?
7. Does the existing Kummer route contain reusable generic mathematics that
   should later be redirected to the new neutral kernel, and which pieces are
   merely FLT receiver/orchestration layers?
8. What is the first honest remaining obstruction after Phase 15?

## Non-goals

Do not in this phase:

- prove arbitrary `TraceOneInt(s_p)` is Dedekind/PID/UFD/Euclidean;
- prove a class group is p-torsion-free for any new prime;
- prove regular-prime criteria or Bernoulli/class-number formulas;
- prove unit p-th-power surjectivity for arbitrary prime-discriminant orders;
- refactor the existing Kummer proof tower wholesale;
- modify FLT3/FLT5/FLT7 endpoints;
- claim a general FLT theorem.
