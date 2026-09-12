# FLT prime-generalization Phase 15 — ideal/class-group arithmetic kernel

## Scope and outcome

This report records the bounded implementation requested by
instruction-015.md. The production module is neutral and imports only
Mathlib; it does not import DkMath.FLT.*, Kummer receivers, or any
fixed-prime FLT target.

Both requested neutral layers are green:

~~~
PGEN-IDEAL-FACTOR-GREEN
PGEN-CLASSGROUP-PRINCIPALIZATION-GREEN
~~~

The phase headline is therefore:

~~~
PGEN-CLASSGROUP-PRINCIPALIZATION-GREEN
~~~

The implementation proves only ideal factor extraction and
class-group-driven principalization. It does not turn a principal ideal
statement into an element p-th-power equality; unit absorption remains a
separate Phase-14 unit-sector obligation.

## A. Pinned Mathlib API audit

The audit was performed against the pinned Mathlib checkout rather than from
remembered signatures.

### Ideal factorization

For [CommRing R] [IsDedekindDomain R], the following declarations are
available:

~~~
Ideal.uniqueFactorizationMonoid
  : UniqueFactorizationMonoid (Ideal R)

Ideal.prod_normalizedFactors_eq_self
  (hI : I ≠ ⊥) : (normalizedFactors I).prod = I

Ideal.count_normalizedFactors_eq
  {p x : Ideal R} [p.IsPrime] {n : ℕ}
  (hle : x ≤ p ^ n) (hlt : ¬ x ≤ p ^ (n + 1)) :
  (normalizedFactors x).count p = n

Ideal.count_normalizedFactors_eq_multiplicity
  : Multiset.count p.asIdeal (normalizedFactors I) =
      multiplicity p.asIdeal I

Ideal.normalizedFactorsEquivSpanNormalizedFactors
  {r : R} (hr : r ≠ 0) :
  {d : R | d ∈ normalizedFactors r} ≃
    {I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R))}
~~~

The ideal carrier also has Ideal.isCoprime_iff_gcd, Ideal.isUnit_iff,
and a Unique (Ideal R)ˣ instance. The latter supplies the
Subsingleton (Ideal R)ˣ requirement of Mathlib's generic
exists_eq_pow_of_mul_eq_pow theorem.

The fractional-ideal factorization declarations are present as:

~~~
FractionalIdeal.finprod_heightOneSpectrum_factorization
FractionalIdeal.finprod_heightOneSpectrum_factorization_principal
~~~

They factor a nonzero fractional ideal by height-one spectra, with integral
numerator/denominator multiplicities. They are useful comparison APIs, but
the new kernel does not need to introduce a fractional-ideal witness.

### Principal ideals and generators

The pinned class-group API contains:

~~~
Submodule.IsPrincipal.generator
Submodule.IsPrincipal.span_singleton_generator
~~~

ClassGroup.mk_eq_one_iff characterizes the class of a nonzero unit
fractional ideal as principal. For nonzero integral ideals in a Dedekind
domain, the direct endpoint is:

~~~
ClassGroup.mk0_eq_one_iff
  (hI : I ∈ (Ideal R)⁰) :
  ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrincipal
~~~

### Class-group construction and powers

The actual declarations are:

~~~
FractionalIdeal.mk0
  : (Ideal R)⁰ →* (FractionalIdeal R⁰ (FractionRing R))ˣ

ClassGroup.mk0
  : (Ideal R)⁰ →* ClassGroup R

ClassGroup.mk0_eq_mk0_iff
ClassGroup.mk0_surjective
ClassGroup.mk_eq_one_iff
~~~

Because ClassGroup.mk0 is a monoid homomorphism, ideal powers pass to
class-group powers through MonoidHom.map_pow. The implementation uses this
explicitly when converting I ^ p principal into
ClassGroup.mk0 ⟨I, hI⟩ ^ p = 1.

The pinned source also contains
IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid.
It is a useful comparison theorem for the UFD-to-PID route, but it is not
needed by the class-group kernel.

## B. Production module

The new neutral module is:

~~~
DkMath/Lib/NumberTheory/IdealPowerFactor.lean
~~~

Its only import is Mathlib. In particular, there is no dependency on
DkMath.FLT.Kummer.ClassGroupBridge or
DkMath.FLT.Kummer.CyclotomicPrincipalization.

### Neutral p-torsion-free predicate

The definition is:

~~~
def classGroupPTorsionFreeAt (R : Type*) (p : ℕ)
    [CommRing R] [IsDomain R] : Prop :=
  ∀ a : ClassGroup R, a ^ p = 1 → a = 1
~~~

The assumptions are the weakest ones needed to form ClassGroup R; the
predicate itself does not require a Dedekind-domain instance.

### Principalization from a class witness

The direct theorem is:

~~~
ideal_isPrincipal_of_classGroupPTorsionFreeAt
~~~

It takes a nonzero integral ideal I, a proof of
classGroupPTorsionFreeAt R p, and
ClassGroup.mk0 ⟨I, hI⟩ ^ p = 1, and returns I.IsPrincipal.

The stronger convenience endpoint is:

~~~
ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
~~~

It proves:

~~~
I ≠ 0
I^p principal
classGroupPTorsionFreeAt R p
--------------------------
I principal
~~~

The proof first establishes that I^p is nonzero, applies
ClassGroup.mk0_eq_one_iff to the principal ideal I^p, and uses
MonoidHom.map_pow to obtain the class-group p-torsion witness. No unit
factor is introduced in this theorem.

## C. Coprime ideal p-th-power extraction

The production wrappers are:

~~~
exists_eq_pow_of_isCoprime_mul_eq_pow
exists_eq_pow_of_isCoprime_mul_eq_pow_right
exists_eq_pow_of_isCoprime_mul_eq_pow_pair
~~~

For a Dedekind-domain ideal carrier they prove:

~~~
I * J = K^p
IsCoprime I J
----------------
∃ A, I = A^p
∃ B, J = B^p
~~~

The wrapper follows the available generic factorization route:

~~~
IsCoprime I J
  -> gcd I J = 1                  [Ideal.isCoprime_iff_gcd]
  -> IsUnit (gcd I J)             [Ideal.isUnit_iff / one]
  -> exists_eq_pow_of_mul_eq_pow  [GCDMonoid + unique ideal units]
~~~

This is an integral-ideal theorem under [IsDedekindDomain R]. No bespoke
normalized-factor proof was required, and no unsupported fractional-ideal
unit argument was introduced.

The test-first probe is:

~~~
DkMathTest/FLT/Prime/IdealPowerFactorAuditProbe.lean
~~~

It checks the left factor, right factor, pair extraction, and the
principalization-from-I^p endpoint without importing an FLT module.

## D. Relation to the Phase-14 element API

The two routes are intentionally separate:

~~~
Element GCD/UFD route
  x*y = z^p + gcd(x,y)=1
    -> x ~ gamma^p
    -> x = delta^p only after unit p-surjectivity

Dedekind ideal route
  (x)(y) = (z)^p + coprime ideals
    -> (x) = A^p
    -> [A]^p = 1
    -> A principal under class-group p-torsion-freeness
    -> element comparison gives unit * gamma^p
    -> exact element equality only after unit-sector control
~~~

Phase 15 formalizes the middle two ideal/class-group arrows. It does not
bridge the final generator comparison or absorb its unit. The existing
Phase-14 declaration
eq_pow_of_associated_pow_of_unit_pow_surjective remains the neutral
element-level unit-sector boundary.

## E. Finite specialization audit

The audit is strict about the carrier. The focused instance probe is:

~~~
DkMathTest/FLT/Prime/IdealPowerFiniteInstantiationAudit.lean
~~~

It imports only the existing arithmetic owners needed to make instance
synthesis observable.

| p | s_p | proved carrier arithmetic | unit sector | axis / conjugate extraction | ideal-route status |
|---:|---:|---|---|---|---|
| 3 | -1 | TraceOneInt (-1) has IsDomain, EuclideanDomain, explicit GCDMonoid, IsPrincipalIdealRing, and IsDedekindDomain after the existing Eisenstein extraction module is imported | norm/unit and cube-up-to-unit APIs exist; no arbitrary neutral unit p-surjectivity claim | generic discrAxis API exists; no dedicated discrAxis irreducible/prime theorem found; Eisenstein conjugate-coprime and cube extraction exist | GREEN for the neutral ideal kernel on this carrier; FLT3 unit/conjugate specialization remains its own route |
| 5 | 1 | GoldenInt has IsDomain, EuclideanDomain, IsPrincipalIdealRing, and IsDedekindDomain; this is not an automatic TraceOneInt 1 instantiation | goldenUnitClassesModFifth exists for GoldenInt; it is a finite sector classification, not fifth-power surjectivity | Golden conjugate-coprime and fifth-power-up-to-unit APIs exist; no TraceOne discrAxis prime theorem is available | GREEN only for the GoldenInt carrier; TraceOneInt 1 transfer is NOT FORMALIZED |
| 7 | -2 | TraceOneInt (-2) has IsDomain, EuclideanDomain, explicit GCDMonoid, IsPrincipalIdealRing, and IsDedekindDomain after the existing quadratic factor module is imported | isUnit_iff_eq_one_or_neg_one and exists_seventh_power_eq_of_isUnit give the specialized seventh-power unit sector | irreducible_sevenAxis, prime_sevenAxis, conjugate-coprime, and seventh-power extraction exist | GREEN for the neutral ideal kernel and the existing p=7 specialized carrier |
| 11 | -3 | only Phase-13 TraceOne coordinate/norm front-end evidence; no proved Euclidean/PID/GCD/Dedekind instance in the audited source set | NOT FORMALIZED | no dedicated axis irreducible/prime or conjugate extraction | NOT FORMALIZED |
| 13 | 3 | only Phase-13 TraceOne coordinate/norm front-end evidence; no proved Euclidean/PID/GCD/Dedekind instance in the audited source set | NOT FORMALIZED | no dedicated axis irreducible/prime or conjugate extraction | NOT FORMALIZED |

The p=3 and p=7 GCDMonoid entries are explicit owner-module instances;
Pinned Mathlib does not synthesize a GCDMonoid directly from a EuclideanDomain
alone in these probes. The p=5 GoldenInt fifth-power theorem similarly
constructs its GCDMonoid locally inside the existing theorem, so the finite
audit does not pretend that a global GoldenInt GCDMonoid instance exists.

No result for p=11 or p=13 is inferred from the Phase-13 norm bridge alone.

## F. Classification and boundary

The achieved classification is:

~~~
PGEN-IDEAL-FACTOR-GREEN
PGEN-CLASSGROUP-PRINCIPALIZATION-GREEN
~~~

The implementation does not prove a general FLT theorem, a general
TraceOneInt Dedekind-domain instance, a class-number theorem, regular-prime
criteria, Kummer descent, class-group vanishing, or unit classification. It
also does not identify ideal generators with element p-th powers without a
separate unit-sector hypothesis.

## Verification

The focused verification consists of:

~~~
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMathTest.FLT.Prime.IdealPowerFactorAuditProbe
lake build DkMathTest.FLT.Prime.IdealPowerFactorAuditAxiomAudit
lake build DkMathTest.FLT.Prime.IdealPowerFiniteInstantiationAudit
~~~

All four targets build successfully. The axiom audit reports only the
standard inherited propext, Classical.choice, and Quot.sound dependencies;
there is no sorryAx or new explicit axiom in the production kernel.
