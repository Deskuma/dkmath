# instruction-006 — LUNA neutral Eisenstein-coordinate core and cubic bridge

## Mission

LUNA-006 is a deterministic library/refactor checkpoint.

ASTRA-001 scratch contains exact Eisenstein-coordinate identities useful for
the balanced-box research frontier:

~~~text
1. norm of beta * gamma^2
2. coefficient-one => coprime quadratic coefficients
~~~

Do NOT copy the scratch-local ad hoc norm into ABC.

The repository already has a neutral quadratic ring:

~~~text
DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)
~~~

with tau^2 = tau - 1 and multiplicative norm.

Since tau = -omega, standard Eisenstein coordinates m+n*omega are represented
by <m,-n> in TraceOneInt (-1).

LUNA-006 should freeze this neutral coordinate presentation and add a thin ABC
bridge for the cubic polynomial.

No factorization-existence theorem is part of this checkpoint.
No counting theorem is part of this checkpoint.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch: wip/ABC-GN-astra-260906-v1
campaign: lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/
~~~

Read:

~~~text
report-005.md
report-004.md
report-001.md
scratch-001.lean
~~~

Inspect:

~~~text
DkMath/NumberTheory/TraceOneQuadratic.lean
DkMath/FLT/GEisensteinBridge.lean
DkMath/FLT/ThreeTraceOneBridge.lean
DkMath/Petal/EisensteinBridge.lean
DkMath/ABC/GNExcessCubicMordellIncidence.lean
~~~

The dependency note in Petal.EisensteinBridge is important: neutral
Eisenstein arithmetic should eventually live below FLT/Petal.

---

## Part I — neutral NumberTheory module

Add:

~~~text
DkMath/NumberTheory/EisensteinCoordinates.lean
~~~

Import only:

~~~text
DkMath.NumberTheory.TraceOneQuadratic
~~~

Namespace recommendation:

~~~text
DkMath.NumberTheory.EisensteinCoordinates
~~~

Do not import FLT, Petal, or ABC.

---

## Part II — standard Eisenstein coordinate embedding

Define:

~~~text
eisensteinCoord (m n : Int) : TraceOneInt (-1) := <m,-n>.
~~~

Document that this represents m+n*omega under tau=-omega.

Provide simp lemmas for fst/snd if useful.

---

## Part III — neutral Eisenstein norm formula

Prove:

~~~text
norm (eisensteinCoord m n)
=
m^2 - m*n + n^2.
~~~

Recommended theorem:

~~~text
norm_eisensteinCoord
~~~

The canonical norm remains the existing TraceOneQuadratic norm.

Do NOT define a second independent norm function unless only as an abbrev.

---

## Part IV — coordinate multiplication formula

Prove:

~~~text
eisensteinCoord a b * eisensteinCoord c d
=
eisensteinCoord
  (a*c - b*d)
  (a*d + b*c - b*d).
~~~

Recommended theorem:

~~~text
eisensteinCoord_mul
~~~

Prove this from the existing TraceOne ring multiplication.

No ring-of-integers theorem is needed.

---

## Part V — square-coordinate formula

Prove:

~~~text
(eisensteinCoord m n)^2
=
eisensteinCoord
  (m^2-n^2)
  (2*m*n-n^2).
~~~

Recommended theorem:

~~~text
eisensteinCoord_sq
~~~

This is one of the exact identities used in ASTRA-001.

---

## Part VI — beta times gamma-square coordinates

For beta=b+c*omega and gamma=m+n*omega, prove:

~~~text
beta * gamma^2
=
A + B*omega
~~~

where:

~~~text
A =
  b*(m^2-n^2)
  -
  c*(2*m*n-n^2)

B =
  b*(2*m*n-n^2)
  +
  c*(m^2-2*m*n).
~~~

Recommended theorem:

~~~text
eisensteinCoord_mul_sq
~~~

Prefer a short consumer of Parts IV/V.

---

## Part VII — norm product identity

Use the existing multiplicative norm theorem and the coordinate formulas to
prove:

~~~text
Norm(A+B*omega)
=
Norm(b+c*omega) * Norm(m+n*omega)^2.
~~~

Recommended theorem:

~~~text
norm_eisensteinCoord_mul_sq
~~~

The public theorem should use the existing TraceOneQuadratic norm.

If cheap, also provide the explicit polynomial corollary:

~~~text
A^2-A*B+B^2
=
(b^2-b*c+c^2) * (m^2-m*n+n^2)^2.
~~~

Do not create an alternate norm API.

---

## Part VIII — coefficient-one coprimality

Let:

~~~text
P = 2*m*n - n^2
Q = m^2 - 2*m*n.
~~~

If:

~~~text
b*P + c*Q = 1,
~~~

prove:

~~~text
IsCoprime P Q.
~~~

Recommended theorem:

~~~text
eisenstein_square_coefficient_coprime
~~~

This is exactly Bezout's identity.

Do not derive counting consequences.

---

## Part IX — thin ABC cubic bridge

Add:

~~~text
DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean
~~~

Import:

~~~text
DkMath.ABC.GNExcessCubicMordellIncidence
DkMath.NumberTheory.EisensteinCoordinates
~~~

This module must be thin.

It must not define a new Eisenstein ring or norm.

---

## Part X — cubic quadratic as fixed Eisenstein norm

For every natural a, prove over Int:

~~~text
a^2 + 3*a + 3
=
Norm((a+2) + omega).
~~~

Use the neutral coordinate embedding:

~~~text
eisensteinCoord ((a:Int)+2) 1.
~~~

Recommended theorem:

~~~text
cubicQuadratic_eq_eisensteinNorm
~~~

A casted Nat-to-Int statement is acceptable.

This is the fixed-ring identity used conceptually in report-001.

---

## Part XI — shell witness factor-product norm wrapper

For a shell witness a, combine:

~~~text
M(a)*S(a) = a^2+3*a+3
~~~

with Part X to prove:

~~~text
(M(a)*S(a) : Int)
=
Norm(eisensteinCoord (a+2) 1).
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm
~~~

This is a direct bridge only.

Do not assert that the Eisenstein element factors as beta*gamma^2.

---

## Part XII — optional coefficient-one implication

Do NOT prove factorization existence.

If short, add a generic implication theorem:

~~~text
eisensteinCoord b c * (eisensteinCoord m n)^2
=
eisensteinCoord ((a:Int)+2) 1
=>
b*(2*m*n-n^2) + c*(m^2-2*m*n) = 1.
~~~

Then derive the coprimality conclusion using Part VIII.

This is optional and is an implication from an explicit equality, not an
existence claim.

---

## Part XIII — compatibility with existing FLT/Petal norm

Do not refactor FLT in this checkpoint.

If cheap, add a theorem showing that the existing shifted natural norm agrees
with the neutral Int coordinate norm on the safe shifted coordinates already
used by FLT/Petal.

Do not change existing public FLT theorem statements.

A larger dependency cleanup belongs to a separate refactor campaign.

---

## Part XIV — negative boundaries

Document explicitly:

~~~text
PROVED:

neutral standard Eisenstein coordinates live inside TraceOneInt (-1).

their norm is m^2-m*n+n^2.

multiplication and square coordinates are exact.

beta*gamma^2 has the ASTRA-001 coordinate formulas.

norm multiplicativity gives the square-product norm identity.

coefficient-one gives a Bezout coprimality theorem.

the cubic quadratic a^2+3a+3 is the norm of (a+2)+omega.

NOT PROVED:

every production cubic witness has a factorization beta*gamma^2.

existence or uniqueness of beta or gamma.

UFD factor extraction for the ABC shell.

represented-pair sparsity.

integral-point counts.

balanced-box power saving.

ABC.
~~~

---

## Part XV — public imports

Add the neutral module to an existing NumberTheory aggregator only if there is
a clear stable aggregator.

Import the ABC bridge from DkMath/ABC.lean immediately after
GNExcessCubicMordellIncidence.

Do not reorder unrelated imports.

Do not make NumberTheory depend on ABC, FLT, or Petal.

---

## Part XVI — report

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-006.md
~~~

Title:

~~~text
# LUNA-006 — neutral Eisenstein-coordinate core and cubic bridge
~~~

Report:

1. files changed
2. neutral dependency direction
3. coordinate embedding
4. norm theorem
5. multiplication formula
6. square formula
7. beta-times-square formula
8. norm product identity
9. coefficient-one coprimality
10. cubic quadratic norm bridge
11. shell witness product norm bridge
12. optional coefficient-one implication status
13. compatibility with existing FLT/Petal API
14. explicit no-factorization-existence boundary
15. focused neutral build
16. focused ABC bridge build
17. ABC aggregator build
18. forbidden scan
19. axiom audit
20. remaining research frontier

Do not include commit hashes.

---

## Part XVII — validation

Run at minimum:

~~~text
lake build DkMath.NumberTheory.EisensteinCoordinates
lake build DkMath.ABC.GNExcessCubicEisensteinCoordinates
lake build DkMath.ABC
~~~

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
norm_eisensteinCoord

eisensteinCoord_mul

eisensteinCoord_sq

eisensteinCoord_mul_sq

norm_eisensteinCoord_mul_sq

eisenstein_square_coefficient_coprime

cubicQuadratic_eq_eisensteinNorm

shell witness product norm bridge.
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

Stop when production DkMath has a neutral, reusable Eisenstein coordinate
presentation backed by TraceOneInt (-1), and ABC can state the cubic quadratic
as that neutral norm.

Do NOT prove beta*gamma^2 factorization existence.
Do NOT count Eisenstein factorizations.
Do NOT begin balanced-box research.
Do NOT open LUNA-007 automatically.
