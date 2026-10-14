# GCNB-003R / instruction-001 — Remove the nonzero-base hypothesis from Norm = GN

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-000.md
- DkMath/CFBRC/CyclotomicNorm.lean
- DkMath/NumberTheory/CyclotomicQRProduct.lean
- DkMath/Lib/Cosmic/GTailCyclotomic.lean

## 1. Mission

GCNB-003 successfully extracted a genuine dependency-neutral algebraic norm
identity:

~~~text
Algebra.norm Z (cyclotomic linear factor) = GN p x u
~~~

but the public theorem currently carries the proof-path hypothesis:

~~~text
u != 0
~~~

because the implementation passes through the rational ratio

~~~text
(x + u) / u.
~~~

The mathematical identity itself is homogeneous and should not need this
division hypothesis.

The goal of this checkpoint is to remove the accidental u != 0 boundary and
finish GCNB-003 as an assumption-free prime cyclotomic Norm = GN theorem in
natural gap/base coordinates.

## 2. Current production API

The current public carrier is:

~~~lean
cyclotomicLinearFactorInRingOfIntegers hζ x u
~~~

representing

~~~text
(x + u) - ζ*u
~~~

in the ring of integers.

The current public norm theorems are:

~~~lean
cyclotomicLinearFactor_norm_eq_GN_ratCast hζ hu0
cyclotomicLinearFactor_norm_eq_GN hζ hu0
~~~

where hu0 : u != 0.

Do not regress the already green theorem surface.

## 3. Preferred proof route: direct homogeneous norm

Prefer removing division entirely rather than merely hiding it.

The intended direct chain is:

~~~text
Algebra.norm_Q ((x+u) - ζ*u)
  = product over Q-embeddings
      ((x+u) - σ(ζ)*u)

  = product over primitive p-th roots μ
      ((x+u) - μ*u)

  = GTailCyclotomicShell p x u

  = GTail p 1 x u

  = GN p x u.
~~~

Existing useful production theorems include:

~~~text
Algebra.norm_eq_prod_embeddings
IsPrimitiveRoot.embeddingsEquivPrimitiveRoots
CyclotomicQRProduct.primitiveRoots_product_eq_shell
GTail_one_eq_GTailCyclotomicShell
cyclotomicRootProduct_eq_shell
cyclotomicRootProduct_eq_GN
~~~

Audit the exact signatures before coding.

The strongest useful neutral helper would be a field norm theorem of the
conceptual form:

~~~lean
theorem cyclotomicLinearFactor_fieldNorm_eq_GN
    ...
    (hζ : IsPrimitiveRoot ζ p) (x u : Nat) :
    Algebra.norm Rat
      (((x + u : Nat) : K) - ζ * (u : K))
      =
      ((GN p x u : Nat) : Rat)
~~~

or an equivalent theorem with explicit algebraMap casts.

This name/signature is only a suggestion.

## 4. Acceptable fallback: explicit u = 0 branch

If a direct homogeneous embedding proof becomes disproportionately invasive,
an explicit by_cases hu : u = 0 proof is acceptable.

For u != 0, reuse the existing theorem.

For u = 0, prove directly that:

~~~text
carrier = x
Norm(x) = x^(p-1)
GN p x 0 = x^(p-1).
~~~

Use existing Algebra.norm_algebraMap / Algebra.coe_norm_int /
IsCyclotomicExtension.finrank and GTail/shell APIs rather than introducing a
new bespoke norm formula.

Do not add a positivity hypothesis.

## 5. Public API target

The final stable public theorem should have no hu0 argument:

~~~lean
theorem cyclotomicLinearFactor_norm_eq_GN
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p x u : Nat} [Fact p.Prime]
    [IsCyclotomicExtension {p} Rat K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Algebra.norm Z
      (cyclotomicLinearFactorInRingOfIntegers hζ x u)
      =
      ((GN p x u : Nat) : Int)
~~~

Likewise, if the rat-cast theorem remains public, prefer removing hu0 from it
too.

To preserve compatibility during the branch, an _of_ne_zero wrapper may be
kept if useful:

~~~text
cyclotomicLinearFactor_norm_eq_GN_of_ne_zero
~~~

but the assumption-free theorem should own the simple canonical name.

## 6. Required boundary regressions

Add tests for at least:

~~~text
p = 3, x = 1, u = 0
p = 5, x = 1, u = 0
p = 7, x = 1, u = 0
~~~

Also test the zero carrier boundary if it elaborates naturally:

~~~text
x = 0, u = 0.
~~~

Retain the existing p = 3,5,7 u = 1 regressions.

The theorem should remain prime-only.

## 7. Strong compatibility target

If the direct homogeneous proof makes it cheap, expose a theorem relating the
field norm to the existing root-product carrier after coefficient embedding.

Conceptually:

~~~text
field Norm of chosen linear factor
  = GN
  = cyclotomicRootProduct
  = GTailCyclotomicShell.
~~~

Do not force a cross-codomain equality if it creates ugly casts. A focused
test proving both sides equal the same GN value is sufficient.

## 8. Do not do GCNB-004 yet

This checkpoint is only the completion of the Norm layer.

Do not add:

- principal ideal p-th-power extraction;
- class-group arguments;
- ideal valuations;
- FLT packet routing;
- TraceOne projection;
- p = 7-specific closure logic.

Those belong to later checkpoints.

## 9. Axiom and dependency rules

No:

~~~text
sorry
admit
sorryAx
new axiom
unsafe proof shortcut
~~~

DkMath.CFBRC must not import the FLT/Kummer stack.

Do not infer field-element equality from equal norms.

Do not replace Algebra.norm by Complex.normSq.

## 10. Validation

Run at least:

~~~text
lake build DkMath.CFBRC.CyclotomicNorm
lake build DkMathTest.CFBRC.CyclotomicNorm
lake build DkMath.CFBRC
lake build DkMath
git diff --check
~~~

Add #print axioms for the final assumption-free public norm theorems.

## 11. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-001.md
~~~

Classify:

### Outcome A — unconditional Norm = GN

The u != 0 boundary is removed and the public theorem is assumption-free.

### Outcome B — direct homogeneous route blocked

Keep the existing theorem unchanged, add no fake generality, and document the
exact Mathlib/API obstruction.

### Outcome C — u = 0 closes only under extra structure

Record the precise extra hypothesis and why it is not acceptable as the stable
generic API.

## 12. Completion gate

If Outcome A is achieved and validation is green, GCNB-003/003R is closed.

Only then should the next instruction open GCNB-004:

~~~text
principal ideal identity and valuation transport
~~~

for the newly stabilized cyclotomic linear-factor carrier.
