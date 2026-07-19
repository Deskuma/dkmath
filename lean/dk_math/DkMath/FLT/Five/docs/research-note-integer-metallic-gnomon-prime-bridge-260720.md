# Integer–Metallic Gnomon–Prime Bridge

Date: 2026-07-20
Status: research note; definitions, algebraic identities, and future formalization targets
Context: FLT5 / GN5 / signed square–golden / golden ramifier route

## 1. Motivation

The FLT5 reduction exposed the integral golden order through the quadratic norm

$$
M^2+MN-N^2.
$$

The same checkpoint identified the ramifier

$$
\tau=2+\varphi,
\qquad
N(\tau)=5.
$$

This suggests recording the more general relation among:

- an integer anchor $k$;
- the metallic ratio determined by $X^2-kX-1=0$;
- the unit gnomon between the integer anchor and the continuous root;
- the discriminant $k^2+4$;
- prime discriminants and ramified norm factors; and
- the GN / cyclotomic structures appearing in FLT-type factorizations.

This note does not assert a general FLT theorem.  It fixes a reusable research map.

## 2. Integer anchor and metallic root

For $k\in\mathbb N$, define

$$
F_k(X)=X^2-kX-1.
$$

At the integer anchor $X=k$,

$$
F_k(k)=-1.
$$

The positive root is

$$
\mu_k=\frac{k+\sqrt{k^2+4}}{2},
$$

and satisfies

$$
F_k(\mu_k)=0,
\qquad
\mu_k^2=k\mu_k+1.
$$

Equivalently,

$$
\mu_k(\mu_k-k)=1,
\qquad
\mu_k-k=\frac{1}{\mu_k}.
$$

Thus the metallic root is the unique positive point at which the product of

the completed scale $\mu_k$ and the displacement from the integer anchor

$\mu_k-k$ is exactly one.

For $k\ge1$,

$$
k<\mu_k<k+1.
$$

Hence each integer cell $[k,k+1]$ contains exactly one unit-gap metallic root.
The positions are not equally spaced.  What is uniform is:

1. one root per integer cell; and
2. the completed gnomon product is always the same unit $1$.

## 3. Cosmic-formula reading

The equation

$$
X^2=kX+1
$$

has the decomposition

$$
\mathrm{Big}=X^2,
\qquad
\mathrm{Body}=kX,
\qquad
\mathrm{Gap}=1.
$$

At $X=k$, Big and Body coincide before the unit Gap is added.  Moving to the
continuous root completes the missing unit through

$$
X(X-k)=1.
$$

This gives the working interpretation:

> A metallic ratio is the continuous completion point of an integer-anchored
> quadratic world whose missing gnomon has unit mass.

## 4. General gap family

For an integer or nonnegative parameter $g$, consider

$$
F_{k,g}(X)=X^2-kX-g.
$$

The positive root is

$$
\rho_{k,g}=\frac{k+\sqrt{k^2+4g}}{2},
$$

and satisfies

$$
\rho_{k,g}(\rho_{k,g}-k)=g.
$$

Thus $g$ is the exact gnomon product between the integer anchor and the
continuous completion point.

The metallic means are the special unit-gap layer $g=1$.

Potential future specializations include:

- $g=1$: metallic unit ratio;
- $g=p$ for a prime $p$: prime-gap ratio;
- $g=GN_d(x,u)$: GN-residual ratio; and
- $g=u^d$: cosmic unit-kernel ratio.

These are research directions, not presently established equivalences with the
FLT reduction tower.

## 5. Discriminant as the gap-to-prime interface

The discriminant of $F_{k,g}$ is

$$
D_{k,g}=k^2+4g.
$$

The Gap enters the discriminant through the exact term $4g$.
Consequently the following structural chain is suggested:

```text
Gap g
  -> discriminant k^2 + 4g
  -> quadratic order / field
  -> ramified primes
  -> norm factors
  -> divisibility and valuation channels
```

For the unit-gap family,

$$
D_k=k^2+4.
$$

If $D_k=p$ is prime, then

$$
\mu_k=\frac{k+\sqrt p}{2}
$$

is a norm-$-1$ unit in the associated quadratic order.

This yields two distinct prime-indexed viewpoints.

### 5.1. Prime integer anchor

Set $k=p$ for a prime $p$ and study

$$
\mu_p^2=p\mu_p+1.
$$

This is the unit-gap continuous completion of the prime scale $p$.

### 5.2. Prime discriminant

Require

$$
p=k^2+4.
$$

Then the quadratic order itself has prime discriminant $p$.
This is the stronger relation relevant to the FLT5 golden-order event.

## 6. Metallic norm and general ramifier family

Let $\mu_k$ satisfy

$$
\mu_k^2=k\mu_k+1.
$$

For an element $a+b\mu_k$, the conjugate norm is

$$
N_k(a+b\mu_k)=a^2+kab-b^2.
$$

The corresponding binary metallic norm is

$$
\operatorname{MetallicNorm}_k(M,N)=M^2+kMN-N^2.
$$

It diagonalizes as

$$
4\operatorname{MetallicNorm}_k(M,N)
=(2M+kN)^2-(k^2+4)N^2.
$$

Define the candidate metallic ramifier

$$
\tau_k=2+k\mu_k.
$$

A direct norm calculation gives

$$
N_k(\tau_k)=k^2+4=D_k.
$$

For $k=1$,

$$
\mu_1=\varphi,
\qquad
\tau_1=2+\varphi,
\qquad
N_1(\tau_1)=5.
$$

This is exactly the ramifier used by the current FLT5 tower.
Therefore the FLT5 element $2+\varphi$ is the first nontrivial member of the
family $\tau_k=2+k\mu_k$.

## 7. Relation to FLT5

The certified FLT5 route currently contains the chain

```text
residual has one 5-adic layer
  -> square–golden norm has discriminant 5
  -> alpha = tau * beta
  -> Norm(tau) = 5
  -> tau does not divide beta
```

At $k=1$, the metallic discriminant is

$$
1^2+4=5.
$$

Thus the following objects coincide in the present exponent-five case:

- the FLT exponent $5$;
- the discriminant of the golden norm;
- the norm of the visible ramifier $\tau$; and
- the unique residual $5$-adic layer removed from $\alpha$.

This coincidence is Lean-certified only for the concrete FLT5 tower already in
the repository.  Its generalization to other exponents remains a research
question.

## 8. Limits of the metallic generalization

For a general odd prime exponent $p$, the homogeneous cyclotomic cofactor

$$
\frac{z^p-y^p}{z-y}
$$

compresses under symmetric square coordinates to a polynomial of degree
$(p-1)/2$.

The case $p=5$ is special because this degree is two.  Therefore the entire
real cyclotomic kernel becomes a quadratic golden norm.

For larger primes, a metallic quadratic order can at most be a quadratic
projection or subfield of the higher-degree real cyclotomic world.  It should
not be assumed to control the full cofactor without an additional theorem.

This separates two generalization axes:

```text
metallic axis:
  quadratic degree fixed, coefficient k varies

FLT prime-exponent axis:
  cyclotomic structure fixed, degree (p-1)/2 varies
```

They coincide completely at $p=5$, $k=1$.

## 9. Formalization candidates

A future independent module could begin with the algebraic layer only.

```lean
def metallicNorm (k M N : ℤ) : ℤ :=
  M ^ 2 + k * M * N - N ^ 2

 theorem four_mul_metallicNorm
    (k M N : ℤ) :
    4 * metallicNorm k M N =
      (2 * M + k * N) ^ 2 - (k ^ 2 + 4) * N ^ 2

 def metallicTau (k : ℤ) : MetallicInt k :=
  ...

 theorem metallicTau_norm :
  norm (metallicTau k) = k ^ 2 + 4
```

Additional research predicates may include:

```lean
def IsPrimeDiscriminantMetallicIndex (k : ℕ) : Prop :=
  Nat.Prime (k ^ 2 + 4)

 def IsMetallicPrimeExponent (p : ℕ) : Prop :=
  ∃ k : ℕ, p = k ^ 2 + 4
```

A separate cyclotomic bridge should state precisely when a metallic quadratic
shadow is a factor, projection, or subfield of the real cyclotomic kernel.

## 10. Research questions

1. Can the family $\tau_k=2+k\mu_k$ be formalized uniformly as a ramifier of
   discriminant $k^2+4$?
2. For which $k$ is $k^2+4$ prime, and what part of the associated arithmetic
   is useful for GN / FLT reductions?
3. Can a GN residual $g$ be sent functorially to the completion root
   $\rho_{k,g}$ while preserving divisibility or valuation information?
4. Is the FLT5 square–golden bridge the degree-two instance of a general real
   cyclotomic square-kernel construction?
5. For $p>5$, can a prime-discriminant metallic subfield isolate one valuation
   channel even though it does not capture the full real cyclotomic field?
6. Can the integer anchor $k$, displacement $u$, and gnomon product
   $(k+u)u=g$ be integrated with DkMath's Big / Body / Gap and unit-kernel APIs?

## 11. Working summary

The central research identity is

$$
X^2-kX-g=0
\quad\Longleftrightarrow\quad
X(X-k)=g.
$$

It binds together:

- an integer anchor;
- a continuous completion ratio;
- a gnomon Gap;
- a discriminant;
- a quadratic norm world; and
- possible prime ramification.

The FLT5 golden-order route is the concrete unit-gap case

$$
k=1,
\qquad
g=1,
\qquad
g=k^2+4=5,
$$

with the final line understood as the discriminant equation
$D=k^2+4g=5$.

This note records the bridge for later investigation without adding it to the
current FLT5 proof obligations.
