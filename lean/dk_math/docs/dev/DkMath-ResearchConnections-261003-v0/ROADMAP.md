# DkMath Research Connections Roadmap — 2026-10-03

Branch: **research/DkMath-ResearchConnections-261003-v0**

Base: **develop** at **f16282e5b44bd5fe5afa1a15d29f1598cae575cd**

This campaign formalizes selected structural connections from the 2026-10-03
whole-repository survey.  It is intentionally incremental and duplication-aware.

## DRC-000 — Bootstrap and source-state freeze

Create the campaign branch and documentation from the exact commit analyzed by
the survey.

Freeze these facts before implementation:

~~~text
base commit:
  f16282e5b44bd5fe5afa1a15d29f1598cae575cd

already present:
  DkMath.NumberTheory.GN_mul_degree

not yet accepted merely from the survey:
  finite-free adjugate landing
  generic CommSemiring GN composition strengthening
  cyclic determinant norm
  prime cyclic glue
  general prime-shell Hensel
  residue-type classification API
  QR element/relative-norm lift
~~~

Status: **completed**.

## DRC-001 — Finite-free lattice landing kernel

Target the survey's highest-priority new abstraction.

First prove the smallest reusable integer-matrix theorem:

~~~text
det M != 0

exists w, M * w = v

iff

forall i, det M divides (adjugate M * v)_i.
~~~

The proof should expose exactly why determinant/norm information alone is
insufficient: the complete adjugate coordinate vector is required for integral
landing.

After the matrix theorem is stable, investigate an optional wrapper for a
finite-free Z-algebra with a chosen basis and multiplication matrix.

Required regression:

- a nontrivial 2 x 2 example;
- a norm-equal but non-divisible example if convenient;
- compatibility calibration against the conceptual role of
  TraceOneLatticeLanding;
- no refactor of the existing TraceOne theorem unless the new API makes the
  replacement obviously smaller and safer.

Status: **completed — Outcome A**.

Implementation: **instruction-001.md** / **report-001.md**.

## DRC-002 — GN product-degree generalization audit

The product-degree identity itself is already production code:

~~~lean
DkMath.NumberTheory.GN_mul_degree
~~~

with Nat coordinates and the hypothesis `0 < x`.

Therefore this checkpoint begins with search, not implementation.

Question:

~~~text
Does DkMath already contain a cancellation-free theorem over CommSemiring
with the same nested GN factorization?
~~~

If yes:

- record the existing theorem;
- add only missing facade/import/calibration if useful;
- do not duplicate it.

If no:

- prove the genuinely stronger generic theorem, preferably directly from the
  finite-sum / polynomial definition rather than by canceling x;
- derive the existing Nat theorem as a compatibility corollary only if doing so
  simplifies the codebase and does not destabilize downstream imports.

The target generic identity is:

~~~text
GN (a * b) x u
  = GN a x u * GN b (x * GN a x u) (u ^ a)
~~~

over the weakest practical commutative semiring assumptions, including x = 0.

Status: **completed — Outcome A**.

Implementation: **instruction-002.md** / **report-002.md**.

## DRC-003 — Cyclic determinant norm

Connect the complete Cosmic Formula carrier with a cyclic shift / cyclic
quotient.

Conceptual target:

~~~text
det (z I - u S) = z^n - u^n
~~~

for cyclic shift S, and hence with z = g + u,

~~~text
det ((g+u) I - u S) = g * GN n g u.
~~~

Prefer reuse of the existing AKS cyclic quotient rather than creating a second
model of Z[T]/(T^n - 1).

Completion requires:

- arbitrary n >= 1;
- no division;
- explicit relation to the current GN / GTail API;
- clear distinction between full cyclic norm and prime cyclotomic shell norm.

Status: **next checkpoint**.

Implementation instructions: **instruction-003.md**.

## DRC-004 — Prime cyclic glue

For prime p, formalize only the integral gluing facts actually needed by later
work.

Conceptual square:

~~~text
Z[C_p]  ->  Z[zeta_p]
  |             |
  v             v
Z       ->      F_p
~~~

Targets include:

- the congruence compatibility condition;
- reconstruction of an integral cyclic element from compatible components;
- p-th-root gluing when both components are genuine p-th powers;
- explicit handling of unit-times-p-th-power variants rather than silently
  dropping unit data.

Do not advertise a Milnor/Rim square theorem until the exact Lean objects and
maps have been fixed.

Status: **open**.

## DRC-005 — General prime-shell Hensel

Generalize the existing cubic non-ramified Hensel-depth infrastructure.

For distinct primes p and q with q not dividing the base, identify the roots of
the prime shell modulo q with nontrivial p-th roots of unity and prove the
simple-root lift where q != p.

Desired outputs:

- root-count criterion where appropriate;
- unique lifting to q^k;
- exact-depth construction;
- explicit separation of the ramified q = p case.

Reuse:

~~~text
DkMath.NumberTheory.GNThreeHenselDepth
DkMath.NumberTheory.GNThreePairedDepth
~~~

Status: **open**.

## DRC-006 — TraceOne residue-type classification

Package the finite residue behavior without identifying all four-state
multiplications.

Targets:

~~~text
TraceOne, even s mod 2  -> split model F2 x F2
TraceOne, odd s mod 2   -> inert model F4
Gaussian mod 2          -> ramified dual-number model
~~~

For odd q, connect the discriminant condition to split / inert / ramified
behavior where existing Mathlib APIs make the statement clean.

The common additive group may be reused; multiplication must remain explicit.

Status: **open**.

## DRC-007 — Cyclotomic QR provenance lift

Strengthen scalar norm compatibility only if the existing provenance packet
contains enough data for an element-level statement.

Desired chain:

~~~text
QR / QNR products
  -> Gauss difference
  -> TraceOne coordinates
  -> element identity in an explicit quadratic subfield
  -> relative norm
  -> ideal transport.
~~~

Do not infer element identity from equality of scalar norms.

Status: **open**.

## DRC-008 — FLT7 current aggregation

This is a parallel downstream track, not a prerequisite for DRC-001 through
DRC-007.

Use only the current packet and current ownership/cutoff infrastructure.

Target progression:

~~~text
current local ownership
  -> aggregate all current prime-ideal exponents
  -> principalization / class-group receiver
  -> unit sector
  -> seventh-power coordinate landing
  -> additive relation preserved
  -> strict descent.
~~~

Do not return to historical/oriented carriers merely because their scalar norms
match current carriers.

Status: **open in parallel**.

## Promotion rule

A research connection is promoted into `DkMath.Lib` only when:

1. its theorem statement is neutral and reusable;
2. the proof is kernel checked;
3. no stronger existing theorem makes it redundant;
4. relevant boundary cases are covered;
5. public endpoints have an axiom audit;
6. the module has focused regressions.

## Stop rules

Stop and report instead of forcing a theorem when:

- the proposed theorem already exists under another name;
- the argument needs cancellation but the intended theorem includes the zero
  boundary;
- determinant zero destroys the landing equivalence;
- a norm statement is being used as an element statement;
- an ideal p-th power is being turned into an element p-th power without unit
  or class-group control;
- a local valuation is being promoted to global aggregation without a checked
  sum/ownership theorem;
- a fixed-prime computation is the only evidence for a generic claim.

## Next document

Proceed with **instruction-003.md** for DRC-003.
