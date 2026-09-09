# instruction-007 — LUNA explicit Eisenstein square-factor consequence bridge

## Mission

LUNA-007 is a deterministic consequence checkpoint.

LUNA-006 productionized the neutral Eisenstein coordinate algebra and the ABC
cubic norm identity.

The remaining research issue is existence of a factorization of the form:

~~~text
(a+2)+omega = beta * gamma^2.
~~~

LUNA-007 must NOT prove that existence.

Instead, it should freeze all immediate kernel-checkable consequences of an
explicit equality:

~~~text
eisensteinCoord b c * (eisensteinCoord m n)^2
=
eisensteinCoord (a+2) 1.
~~~

This creates a clean production interface for future research.

No factor search.
No UFD theorem.
No counting theorem.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch: wip/ABC-GN-astra-260906-v1
campaign: lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read:

~~~text
report-006.md
report-001.md
scratch-001.lean
~~~

Inspect:

~~~text
DkMath/NumberTheory/EisensteinCoordinates.lean
DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean
DkMath/ABC/GNExcessCubicMordellIncidence.lean
~~~

Treat production Lean as authoritative.

---

## Part I — neutral coordinate consequence theorem

Prefer to extend:

~~~text
DkMath/NumberTheory/EisensteinCoordinates.lean
~~~

unless a separate small neutral module is cleaner.

For integers a,b,c,m,n, assume:

~~~text
hfac :
  eisensteinCoord b c * (eisensteinCoord m n)^2
  =
  eisensteinCoord (a+2) 1.
~~~

Use the existing theorem eisensteinCoord_mul_sq to prove the exact coordinate
equations:

~~~text
b*(m^2-n^2) - c*(2*m*n-n^2)
=
a+2

b*(2*m*n-n^2) + c*(m^2-2*m*n)
=
1.
~~~

Recommended theorem names:

~~~text
eisenstein_mul_sq_eq_cubicCoord_fst
eisenstein_mul_sq_eq_cubicCoord_snd
~~~

or one conjunction theorem plus thin projections.

The second equation is the key coefficient-one identity.

Do not introduce a factorization structure unless absolutely necessary.

---

## Part II — automatic coprimality consequence

From the second coordinate equation, derive:

~~~text
IsCoprime
  (2*m*n-n^2)
  (m^2-2*m*n).
~~~

Recommended theorem:

~~~text
eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime
~~~

This should be a short consumer of:

~~~text
eisenstein_square_coefficient_coprime.
~~~

This theorem is conditional on the explicit factor equality.

It does not prove that such b,c,m,n exist.

---

## Part III — norm factor consequence

Under the same explicit factor equality, prove:

~~~text
Norm(eisensteinCoord (a+2) 1)
=
Norm(eisensteinCoord b c)
  *
Norm(eisensteinCoord m n)^2.
~~~

Recommended theorem:

~~~text
eisenstein_mul_sq_eq_cubicCoord_norm
~~~

Prefer a proof using hfac and norm_eisensteinCoord_mul_sq rather than
polynomial re-expansion.

---

## Part IV — explicit polynomial norm consequence

Derive:

~~~text
a^2 + 3*a + 3
=
(b^2-b*c+c^2)
*
(m^2-m*n+n^2)^2.
~~~

over integers.

Recommended theorem:

~~~text
eisenstein_mul_sq_eq_cubicCoord_polynomial_norm
~~~

For the neutral theorem use a : Int.

Do not add positivity assumptions unless required.

---

## Part V — thin ABC factor-equality bridge

Add:

~~~text
DkMath/ABC/GNExcessCubicEisensteinFactorConsequences.lean
~~~

Import:

~~~text
DkMath.ABC.GNExcessCubicEisensteinCoordinates
~~~

This module should contain only conditional consequences for the cubic shell.

---

## Part VI — shell witness explicit-factor norm packet

For a shell witness a, assume an explicit equality:

~~~text
hfac :
  eisensteinCoord b c * (eisensteinCoord m n)^2
  =
  eisensteinCoord ((a:Int)+2) 1.
~~~

Prove together or separately:

~~~text
1. coefficient-one equation;

2. IsCoprime
     (2*m*n-n^2)
     (m^2-2*m*n);

3. ((M(a)*S(a) : Nat) : Int)
   =
   Norm(eisensteinCoord b c)
   *
   Norm(eisensteinCoord m n)^2.
~~~

Recommended theorem names:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coeff_one

GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coefficients_isCoprime

GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_norm
~~~

The norm theorem should consume:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm
~~~

and the neutral factor norm theorem.

No re-proof of the complement product identity.

---

## Part VII — optional single conjunction packet

Only if useful, expose one theorem returning a conjunction of:

~~~text
first coordinate equation
second coordinate equation
IsCoprime P Q
norm factor equation
~~~

for a shell witness plus explicit factor equality.

This may be convenient for future research.

However:

- do not define a provider;
- do not define a global conjecture;
- do not define a structure implying existence.

A theorem with an explicit hfac hypothesis is preferred.

---

## Part VIII — no converse

Do NOT prove or state:

~~~text
Norm factorization
=>
element factorization.
~~~

Do NOT infer factor equality merely from:

~~~text
a^2+3a+3
=
Norm(beta)*Norm(gamma)^2.
~~~

Norm equality loses unit/associate information.

This boundary should be documented explicitly.

---

## Part IX — no existence theorem

Do NOT add any theorem of the form:

~~~text
exists b c m n,
  eisensteinCoord b c * (eisensteinCoord m n)^2
  =
  eisensteinCoord ((a:Int)+2) 1.
~~~

Do NOT use Classical.choose to manufacture factor coordinates from a weaker
statement.

Do NOT add an axiom or provider for this existence.

The research frontier remains exactly the existence / counting problem.

---

## Part X — optional nonzero consequences

Only if trivial from the explicit equality and needed later, derive safe
nonzero statements.

Do not grow this into a unit classification or UFD development.

This part is optional.

---

## Part XI — public import

Import:

~~~text
DkMath.ABC.GNExcessCubicEisensteinFactorConsequences
~~~

from:

~~~text
DkMath/ABC.lean
~~~

immediately after:

~~~text
GNExcessCubicEisensteinCoordinates.
~~~

Do not reorder unrelated imports.

The neutral consequences remain below ABC.

---

## Part XII — report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-007.md
~~~

Title:

~~~text
# LUNA-007 — explicit Eisenstein square-factor consequence bridge
~~~

Report:

1. files changed
2. exact factor-equality hypothesis
3. first coordinate consequence
4. coefficient-one consequence
5. coprimality consequence
6. norm factor consequence
7. polynomial norm consequence
8. shell witness bridge
9. optional conjunction packet status
10. explicit no-converse boundary
11. explicit no-existence boundary
12. focused neutral build
13. focused ABC bridge build
14. ABC aggregator build
15. forbidden scan
16. axiom audit
17. remaining research frontier

Do not include commit hashes.

---

## Part XIII — validation

Run at minimum:

~~~text
lake build DkMath.NumberTheory.EisensteinCoordinates
lake build DkMath.ABC.GNExcessCubicEisensteinFactorConsequences
lake build DkMath.ABC
~~~

If a new neutral module is used instead of extending the existing file, build
that module explicitly too.

Scan changed production Lean for:

~~~text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
~~~

No new occurrences.

Audit principal declarations:

~~~text
coordinate consequences
coprimality consequence
norm consequence
shell witness norm consequence.
~~~

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

---

## Stop condition

Stop when production Lean can say:

~~~text
IF
  beta * gamma^2 = (a+2)+omega

THEN
  the exact coordinate equations hold,
  the square coefficients are coprime,
  and
  a^2+3a+3 = Norm(beta)*Norm(gamma)^2.
~~~

Do NOT prove the IF hypothesis exists.
Do NOT search for factors.
Do NOT count factors.
Do NOT begin balanced-box research.
Do NOT open LUNA-008 automatically.
