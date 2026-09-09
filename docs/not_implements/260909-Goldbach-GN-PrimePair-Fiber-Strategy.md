# Goldbach via GN Prime-Pair Fiber — Strategy Note

Date: 2026-09-09  
Status: finite GN-fiber reductions implemented; universal paired-fiber escape unresolved
Target branch: `develop`  
Suggested future branch: `wip/NumberTheory-Goldbach-GNFiber-260910-v0`
cid: `6aa15236-f2b0-83ee-bfbf-a1b3c5615e5d`

Implementation follow-up (2026-09-10):
[`NumberTheory-Goldbach-GNFiber-260910-v0`](../../lean/dk_math/docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/README.md).
The original strategy below is retained as the research proposal. The follow-up
distinguishes proved finite reductions, counterexamples to stronger shortcuts,
and the still-missing universal escape provider.

## 1. Purpose

This note preserves the current strategy before implementation begins.

The immediate observation is that DkMath already contains many of the structural tools needed to reformulate the strong Goldbach conjecture inside the GN / Cosmic Formula framework:

- canonical GN / GTail decomposition;
- prime-row Pascal divisibility;
- composite-degree factorization of GN;
- finite positive representation bounds;
- prime-target residue constraints;
- finite prime-world residue spaces;
- Primitive Conservation Kernel machinery.

The remaining task is not to collect more isolated lemmas first, but to choose a proof architecture that forces a prime-pair point to survive on every square fiber.

## 2. Important correction: “all primes are representable by GN” is too weak

For the canonical degree-two kernel,

```text
GN 2 x u = x + 2u.
```

Hence every odd number \(P\) has the trivial positive representation

$$
P = GN_2\!\left(1,\frac{P-1}{2}\right).
$$

Therefore the statement

$$
\forall P>2,\quad \operatorname{Prime}(P)
\to
\exists d,x,u,\quad GN_d(x,u)=P
$$

is not strong enough to imply Goldbach. In fact degree \(2\) already represents every odd target, not only primes.

The Goldbach problem must keep the **fiber center fixed**.

## 3. Goldbach as a degree-two GN fiber theorem

For an even target \(2n\), write

$$
p=n-u,\qquad q=n+u.
$$

Set

$$
x:=n-u.
$$

Then

$$
x+u=n
$$

and

$$
GN_2(x,u)=x+2u=n+u.
$$

Therefore the strong Goldbach statement at \(2n\) is equivalent to the existence of a degree-two GN point satisfying

$$
x+u=n,
\qquad
\operatorname{Prime}(x),
\qquad
\operatorname{Prime}(GN_2(x,u)).
$$

Suggested predicate:

```lean
def GoldbachGNFiberAt (n : ℕ) : Prop :=
  ∃ x u : ℕ,
    x + u = n ∧
    Nat.Prime x ∧
    Nat.Prime (DkMath.CosmicFormulaBinom.GN 2 x u)
```

The first formal checkpoint should prove an exact equivalence between the usual prime-pair statement and this GN-fiber statement.

## 4. Body / Big / Gap interpretation

The degree-two Cosmic Formula gives

$$
(x+u)^2=x(x+2u)+u^2.
$$

With \(n=x+u\),

$$
n^2=(n-u)(n+u)+u^2.
$$

Hence

$$
\mathrm{Big}=n^2,
\qquad
\mathrm{Gap}=u^2,
\qquad
\mathrm{Body}=n^2-u^2=(n-u)(n+u).
$$

Goldbach becomes:

> For every \(n\ge2\), the square fiber
>
> $$
> \mathrm{Body}_n(u)=n^2-u^2
> $$
>
> contains at least one point whose two canonical factors are both prime.

This is the preferred DkMath reading.

## 5. Existing DkMath weapons

### 5.1 Pascal prime-row divisibility

Existing NumberTheory APIs include:

```text
prime_dvd_inner_choose
prime_allInnerWeightedTermDivisible
prime_dvd_weightedBinomialInnerBeamSum
prime_inner_choose_eq_zero_zmod
```

For prime row \(p\),

$$
0<k<p
\Longrightarrow
p\mid\binom pk,
$$

so the inner Pascal Beam vanishes modulo \(p\).

This supplies a canonical prime-row residue pattern.

### 5.2 Composite-degree GN factorization

`DkMath.NumberTheory.GNDegreeFactorization` already proves

```lean
theorem GN_mul_degree
```

with mathematical content

$$
GN_{ab}(x,u)
=
GN_a(x,u)\,
GN_b\!\left(x\,GN_a(x,u),u^a\right).
$$

The second factor is evaluated in transported coordinates; the formula is not a naive same-coordinate product.

The same module already proves:

```text
one_lt_factors_of_composite_degree
not_prime_GN_of_mul_degree
prime_degree_of_prime_GN
GNPositiveRepresentation.degree_prime_of_target_prime
```

Thus, in the positive nondegenerate region,

$$
GN_d(x,u)\text{ prime}
\Longrightarrow
d\text{ prime}.
$$

### 5.3 Prime-target fiber constraints

`DkMath.NumberTheory.GNPrimeTargetResidue` already proves:

```text
GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime
GNPositiveRepresentation.target_modEq_one_degree_of_target_prime
GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
GNPositiveRepresentation.prime_degree_constraints
```

For a positive representation

$$
GN_d(x,u)=P,
\qquad
P\text{ prime},
$$

the existing constraints include

$$
d\text{ prime},
\qquad
d\mid P-1,
\qquad
2^d-1\le P.
$$

Thus the prime-target degree fiber is already very thin.

### 5.4 Finite coordinate bounds

`DkMath.NumberTheory.GNRepresentationBounds` provides

```text
GNPositiveRepresentation.bounds
GNRepresentationBox
GNPositiveRepresentations
mem_GNPositiveRepresentations_iff
```

For

$$
GN_d(x,u)=P
$$

in the positive region,

$$
2^d-1\le P,
\qquad
x^{d-1}<P,
\qquad
d\,u^{d-1}<P,
$$

and in particular

$$
d<P,\qquad x<P,\qquad u<P.
$$

This gives an executable finite search surface.

### 5.5 Primitive / prime-world infrastructure

The public `DkMath.NumberTheory.Primitive` facade already exposes:

```text
FinitePrimeWorld
PeriodicPrimeWorld
PrimeWorldRefinement
PrimeWorldResidues
PrimeWorldCardinality
EulerTotientBridge
PHZ30
SquareBody
SquarePrimeExpansion
PrimitiveConservationKernel
```

These modules are the natural substrate for a Goldbach paired-residue layer.

## 6. The real obstruction problem

For fixed \(n\), define the left and right coordinates

$$
L_n(u):=n-u,
\qquad
R_n(u):=n+u.
$$

A candidate \(u\) fails Goldbach if at least one side is composite.

For a prime \(r\), the local forbidden conditions are

$$
r\mid n-u
\quad\Longleftrightarrow\quad
u\equiv n\pmod r,
$$

and

$$
r\mid n+u
\quad\Longleftrightarrow\quad
u\equiv -n\pmod r.
$$

Thus each prime direction normally removes at most two residue classes from the \(u\)-fiber.

This suggests a paired finite-world object.

Suggested definitions:

```lean
def GoldbachLeftObstructed  (n r u : ℕ) : Prop := r ∣ n - u
def GoldbachRightObstructed (n r u : ℕ) : Prop := r ∣ n + u
def GoldbachObstructed      (n r u : ℕ) : Prop :=
  GoldbachLeftObstructed n r u ∨ GoldbachRightObstructed n r u
```

and eventually a canonical finite paired residue space analogous to `primeWorldResidues`.

## 7. Finite reduction by small prime divisors

If \(m>1\) is composite, then \(m\) has a prime divisor at most \(\sqrt m\).

Since on the Goldbach fiber

$$
n-u\le 2n,
\qquad
n+u\le2n,
$$

every composite side has a small prime witness bounded by roughly

$$
r\le\sqrt{2n}.
$$

Therefore, for fixed \(n\), a hypothetical Goldbach failure can be converted into a finite covering statement:

> every \(u\) in the admissible fiber is covered by at least one small-prime left/right obstruction.

This is the key finite reduction.

The desired contradiction route is then not “prove primality directly”, but:

$$
\text{Goldbach failure}
\Longrightarrow
\text{finite obstruction cover}
\Longrightarrow
\text{capacity / conservation contradiction}.
$$

## 8. Proposed paired-prime-world layer

A future implementation should introduce a finite residue structure for the pair

$$
(n-u,\;n+u).
$$

For a finite known-prime set \(S\), define survivors satisfying

$$
\forall r\in S,\quad
r\nmid(n-u)\land r\nmid(n+u),
$$

with endpoint exceptions handled explicitly when one side itself equals \(r\).

The period should be controlled by

$$
M=\prod_{r\in S}r.
$$

CRT then makes the obstruction pattern periodic.

This is conceptually a two-sided / paired version of the existing PHZ / PrimeWorld machinery.

Possible future names:

```text
GoldbachPrimeWorld
GoldbachPrimeWorldResidues
GoldbachPrimeWorldRefinement
GoldbachPrimeWorldCardinality
GoldbachPairedPHZ
```

## 9. Main strategic theorem shape

The target is not a naive sieve density statement. The decisive theorem should have the shape:

$$
\text{finite old-prime obstruction capacity}
<
\text{Goldbach fiber capacity}.
$$

Equivalently, at least one fiber seat must escape all old-prime obstructions.

That escaping seat should then be forced, using the small-prime-divisor bound, to yield

$$
\operatorname{Prime}(n-u)
\land
\operatorname{Prime}(n+u).
$$

This is where Primitive Conservation Kernel ideas may be able to break the ordinary sieve parity barrier.

## 10. Parity barrier warning

A plain density heuristic such as

$$
\prod_{r\le\sqrt{2n}}
\left(1-\frac{2}{r}\right)
$$

is not by itself a proof strategy. Classical sieve methods face the parity problem precisely when trying to distinguish “no small prime factor” from genuine primality in paired settings.

Therefore the DkMath route must seek an additional structural invariant, not merely a sharper counting estimate.

Candidate extra structure:

- Primitive Conservation Kernel escape;
- exact paired incidence capacity;
- prime-wave conservation;
- GN / GTail \(q\)-adic signatures;
- transport of prime-target residue patterns;
- square-Body conservation across the \(u\)-fiber.

## 11. Higher-degree GN as a classifier, not the direct Goldbach equation

Goldbach itself lives naturally at \(d=2\).

Higher-degree GN remains relevant as a prime-pattern classifier.

For a prime target \(P\), define conceptually

$$
\Sigma(P)
=
\{q\text{ prime}:
\exists x,u,\ GN_q(x,u)=P\}.
$$

Existing DkMath theorems force

$$
q\mid P-1
$$

and

$$
2^q-1\le P.
$$

Thus \(\Sigma(P)\) is finite and thin.

The possible research question is whether the higher-degree GN / GTail signature of

$$
P=n-u
$$

constrains or transports to

$$
Q=n+u.
$$

A conserved signature across the degree-two Goldbach fiber could provide the missing structure beyond ordinary sieve theory.

## 12. Suggested first implementation checkpoints

Future branch:

```text
NumberTheory-Goldbach-GNFiber-v0
```

Suggested sequence:

1. `GoldbachGNFiberAt`
2. exact equivalence with the standard Goldbach pair statement
3. `goldbachBody_eq_square_sub_square`
4. left/right obstruction predicates
5. small-prime obstruction witness for composite endpoints
6. finite obstruction-prime set up to the required square-root bound
7. paired residue space over a finite prime world
8. CRT / periodicity theorem
9. exact local forbidden-seat count
10. global incidence / capacity bound
11. Primitive Conservation Kernel bridge
12. survivor \(\Rightarrow\) prime-pair closure
13. final Goldbach endpoint, only if the previous conservation theorem closes

## 13. Stop / success criteria

Do not claim progress toward Goldbach merely from any of the following:

- all odd primes are representable by \(GN_2\);
- prime-row Pascal divisibility;
- finite residue survival for a fixed primorial;
- numerical verification over large ranges;
- positive heuristic density.

The branch becomes mathematically decisive only when it proves or refutes the universal paired-fiber survival statement.

The critical unresolved theorem is:

$$
\boxed{
\forall n\ge2,\;
\exists u<n,\;
\operatorname{Prime}(n-u)
\land
\operatorname{Prime}(n+u)
}
$$

or the exactly equivalent GN form.

## 14. Current assessment

DkMath now appears to have enough infrastructure to make this a concrete formal research program rather than a speculative analogy.

The strongest current strategic advantage is the combination of:

$$
\text{finite fiber}
+
\text{exact residue obstruction}
+
\text{PrimeWorld periodicity}
+
\text{Primitive conservation}.
$$

The main unknown is whether the conservation layer is strong enough to rule out a complete two-sided obstruction cover for every \(n\).

That is the next real decision point.
