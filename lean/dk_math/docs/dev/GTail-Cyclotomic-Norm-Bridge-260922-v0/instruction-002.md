# GCNB-004 / instruction-002 — Principal ideal and global valuation transport

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-000.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-001.md
- DkMath/CFBRC/CyclotomicNorm.lean
- DkMath/CFBRC/Bridge.lean
- DkMath/CFBRC/CyclotomicProduct.lean
- DkMath/Lib/NumberTheory/PrincipalIdealPower.lean
- DkMath/NumberTheory/TraceOneIdealPower.lean

## 1. Mission

GCNB-003/003R established an assumption-free generic prime cyclotomic carrier

~~~text
alpha = (x + u) - zeta*u
~~~

in the ring of integers of a cyclotomic extension, with

~~~text
Algebra.norm Z alpha = GN p x u.
~~~

GCNB-002 separately retained the complete gap identity

~~~text
x * GN p x u = (x + u)^p - u^p.
~~~

The next step is to place the chosen carrier into the ideal layer without
losing either fact.

This checkpoint must build the first neutral bridge

~~~text
alpha
  -> principal ideal I = (alpha)
  -> Ideal.absNorm I = GN p x u
  -> x * Ideal.absNorm I = (x+u)^p - u^p
  -> rational-prime divisibility / padicValNat transport.
~~~

Do not infer that I itself is a p-th power ideal merely because its norm is a
p-th power.

## 2. Recommended module placement

Prefer a new neutral module:

~~~text
DkMath/CFBRC/CyclotomicIdeal.lean
~~~

with imports no stronger than necessary, likely including:

~~~text
DkMath.CFBRC.CyclotomicNorm
DkMath.CFBRC.Bridge
Mathlib.RingTheory.Ideal.Norm.AbsNorm
~~~

Then export it from DkMath/CFBRC.lean and add a focused test module under
DkMathTest/CFBRC.

Do not import DkMath.FLT.Kummer.* into CFBRC.

## 3. Canonical principal ideal

Introduce the principal ideal of the chosen linear factor, conceptually:

~~~lean
def cyclotomicLinearFactorIdeal
    ...
    (hζ : IsPrimitiveRoot ζ p) (x u : Nat) : Ideal (O K) :=
  Ideal.span
    ({cyclotomicLinearFactorInRingOfIntegers hζ x u} : Set (O K))
~~~

The exact name may be adjusted for local style.

This should be a thin semantic carrier, not a new ideal theory.

## 4. Exact absolute ideal norm

Use the existing production theorem

~~~text
cyclotomicLinearFactor_norm_eq_GN
~~~

and Mathlib's

~~~text
Ideal.absNorm_span_singleton
~~~

to prove the canonical theorem:

~~~text
Ideal.absNorm (cyclotomicLinearFactorIdeal hζ x u)
  = GN p x u.
~~~

This theorem should be unconditional in x and u, matching GCNB-003R.

Do not recompute the field norm from scratch.

Expected proof shape is essentially:

~~~text
absNorm(span(alpha))
  = natAbs(Algebra.norm Z alpha)
  = natAbs((GN p x u : Z))
  = GN p x u.
~~~

Use the actual pinned theorem signatures.

## 5. Preserve the complete gap product

The FLT7 handoff explicitly required that the bridge not forget the boundary
factor.

Therefore prove a theorem of the conceptual form:

~~~text
x * Ideal.absNorm (cyclotomicLinearFactorIdeal hζ x u)
  = (x + u)^p - u^p.
~~~

Derive it from:

~~~text
Ideal.absNorm I = GN p x u
add_pow_eq_mul_GTail_one_add_gap
GN = GTail p 1
~~~

or the existing CFBRC complete-gap theorem.

This is a key deliverable.

Important: do **not** claim that the complete product x*GN is itself the
field norm of x*alpha. In degree p-1,

~~~text
Norm(x*alpha) = x^(p-1) * GN,
~~~

not x*GN.

Keep this distinction explicit in docstrings/report.

## 6. Divisibility transport at the rational norm level

Expose lightweight exact rewrites such as:

~~~text
q ∣ Ideal.absNorm I  <->  q ∣ GN p x u
~~~

and, where useful,

~~~text
q ∣ ((x+u)^p - u^p)
  <-> q ∣ x * Ideal.absNorm I.
~~~

The second equivalence may simply be rewriting the complete-gap identity.

Do not yet choose a prime ideal above q.

## 7. Global p-adic valuation transport

At minimum expose:

~~~text
padicValNat q (Ideal.absNorm I)
  = padicValNat q (GN p x u).
~~~

This is an exact rewrite via absNorm = GN and should require no new arithmetic
hypotheses.

Then connect to the existing CFBRC valuation theorem where its hypotheses are
satisfied.

For example, for prime q with q not dividing x and positive x,u, prove a
theorem of the conceptual form:

~~~text
padicValNat q (Ideal.absNorm I)
  =
padicValNat q ((x+u)^p - u^p).
~~~

Reuse:

~~~text
padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
~~~

rather than re-proving LTE / GN valuation facts.

A corresponding coprime/boundary wrapper may be added if it stays small and
directly reuses DkMath.CFBRC.Bridge.

## 8. Optional aggregate ideal-factor audit

After the exact absNorm and global padicValNat bridges are green, audit the
pinned Dedekind APIs for the next layer:

~~~text
UniqueFactorizationMonoid.normalizedFactors (Ideal (O K))
Ideal.prod_normalizedFactors_eq_self
Ideal.count_normalizedFactors_eq_multiplicity
Ideal.absNorm multiplicativity
~~~

Determine whether one can cleanly express the rational q-adic valuation of
absNorm I as an aggregate over prime-ideal factors whose absolute norm is
divisible by q.

Do not force a theorem here.

If the local-prime aggregate theorem is not nearly immediate, record its exact
shape and API boundary in report-002 and defer it to a follow-up GCNB-004L
checkpoint.

## 9. Critical firewall: global norm valuation is not local ideal valuation

Keep these distinct:

~~~text
padicValNat q (Ideal.absNorm I)
~~~

versus

~~~text
multiplicity / exponent of a particular prime ideal P in I.
~~~

The former is an aggregate rational-prime quantity.

The latter requires a chosen P above q and may involve residue degree / ideal
norm data.

Do not equate them without a checked theorem.

This distinction is especially important for the future FLT7 degree-six
carrier application.

## 10. No p-th-power ideal inference

Even if later FLT data gives

~~~text
GN p x u = b^p
~~~

you may conclude immediately only that

~~~text
Ideal.absNorm I = b^p.
~~~

You may **not** conclude

~~~text
I = J^p
~~~

without separate pairwise-coprime / factorization / class-group input.

Existing modules such as PrincipalIdealPower are consumers after an ideal power
identity is established; they do not manufacture that identity from a norm
power.

## 11. Tests

Add focused tests for p = 3,5,7 in canonical CyclotomicField p Q.

Required checks:

~~~text
absNorm principal ideal = GN
gap * absNorm principal ideal = power difference
padicValNat absNorm = padicValNat GN
~~~

Include at least one u = 0 boundary regression to ensure GCNB-003R remains
visible through the ideal layer.

For valuation-to-difference regression, use a small example satisfying the
existing positivity and q-not-dividing-gap hypotheses; do not manufacture an
FLT counterexample.

Add #print axioms for all new public theorems.

## 12. Validation

Run at least:

~~~text
lake build DkMath.CFBRC.CyclotomicIdeal
lake build DkMathTest.CFBRC.CyclotomicIdeal
lake build DkMath.CFBRC
lake build DkMath
git diff --check
~~~

Scan changed Lean files for:

~~~text
sorry
admit
sorryAx
unsafe
new axiom
~~~

The pre-existing ZsigmondyCyclotomicResearch warning is outside this
checkpoint unless the changed dependency surface unexpectedly reaches it.

## 13. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-002.md
~~~

Classify the result:

### Outcome A — principal ideal + global valuation bridge complete

The principal ideal carrier, exact absNorm = GN, complete-gap absNorm identity,
and rational q-adic valuation transport are kernel checked.

### Outcome B — exact ideal norm complete, valuation composition partial

The principal ideal and absNorm layers are complete, but a desired CFBRC
valuation wrapper requires extra hypotheses or API glue. Record the precise
boundary.

### Outcome C — local ideal valuation was the blocker

Do not weaken or fake the global theorem. Record the exact missing
prime-ideal/residue-degree API and propose a bounded GCNB-004L checkpoint.

## 14. Completion gate

GCNB-004 is complete once the new cyclotomic carrier has a stable principal
ideal API with:

~~~text
Ideal.absNorm I = GN
x * Ideal.absNorm I = power difference
global padicValNat transport
~~~

Local prime-ideal multiplicity ownership may be deferred.

Only after this should the campaign connect the ideal carrier to generic FLT
Prime/TraceOne packets.
