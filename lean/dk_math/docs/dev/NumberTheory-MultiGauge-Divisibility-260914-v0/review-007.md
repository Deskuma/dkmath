# Review 007 — MG-004B general TraceOne lattice landing

## Verdict

**APPROVED — Outcome A: GENERAL TRACEONE LANDING ESTABLISHED**

The implementation closes the intended neutral lattice-landing receiver for
arbitrary `TraceOneInt s` under the exact hypothesis that the divisor norm is
nonzero.

No repair checkpoint is required.

## What was verified

Production file:

```text
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
```

The module correctly avoids the false general statement

```text
beta != 0 -> norm beta != 0
```

and instead keeps

```text
norm beta != 0
```

as the cancellation hypothesis.

This distinction is essential: the production regression at `s = 0` proves
that `tau 0` is nonzero while its norm is zero.

## Coordinate formulas

For

```text
alpha = <a,b>
beta  = <c,d>
```

in `TraceOneInt s`, the implementation proves the exact conjugate-product
coordinates

```text
(alpha * conj beta).fst = a*c + a*d - s*b*d
(alpha * conj beta).snd = b*c - a*d.
```

These formulas agree with the existing multiplication and conjugation
conventions in `TraceOneQuadratic`.

## Nonzero-norm cancellation

The theorem

```text
traceOne_mul_right_cancel_of_norm_ne_zero
```

is a genuine coordinate-determinant argument.

For a zero product `(p,q)*(c,d)=0`, the two coordinate equations imply

```text
p * norm(c,d) = 0
q * norm(c,d) = 0.
```

Thus `norm(c,d) != 0` forces `p=q=0`.  No positive-definite norm argument,
field embedding, Euclidean-domain instance, or integral-domain instance is
smuggled into the proof.

This is the correct general replacement for the positive-definite
`s = -1` cancellation used in MG-004A.

## Main receiver theorem

The public theorem

```text
traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
```

proves, under `norm beta != 0`,

```text
beta | alpha
<->
norm beta | (alpha * conj beta).fst
and
norm beta | (alpha * conj beta).snd.
```

The forward direction is unconditional and reads coordinates after multiplying
an existing quotient by the conjugate.

The reverse direction reconstructs a quotient from the two integer divisibility
witnesses and cancels `conj beta` using the nonzero-norm cancellation theorem.

The explicit polynomial-coordinate corollary is also a real theorem, not a
separate arithmetic API.

## Norm-only boundary

The implementation correctly keeps

```text
beta | alpha -> norm beta | norm alpha
```

as a necessary condition only.  It does not assert a converse.

MG-004A already contains a concrete Eisenstein counterexample to the converse,
and MG-004B adds no conflicting claim.

## Eisenstein specialization

The existing MG-004A public API remains stable.  The new specialization
regression checks that the generic theorem reproduces the approved Eisenstein
coordinate criterion under the convention

```text
eisensteinCoord a b = <a,-b>.
```

This is the right migration pattern: generic theorem first, concrete API kept
stable, no churn forced into the already-approved consumer surface.

## MG-004C boundary

The lattice layer is now complete enough to separate the next filter:

```text
norm divisibility
-> coordinate divisibility
-> integral quotient exists
-> quotient lies in a power/Core image.
```

The final implication is strictly stronger than lattice landing and should be
implemented as a separate receiver layer.

For square/Core landing, if

```text
gamma = <m,n> : TraceOneInt s
```

then

```text
gamma^2 = <m^2 + s*n^2, 2*m*n + n^2>.
```

Hence, for `norm beta != 0`, a natural exact target is

```text
exists gamma, alpha = beta * gamma^2
<->
exists m n,
  (alpha * conj beta).fst = norm beta * (m^2 + s*n^2)
  and
  (alpha * conj beta).snd = norm beta * (2*m*n + n^2).
```

This theorem would compose the completed lattice receiver with the square
image condition without asserting existence of square roots.

A clean strictness regression is available already at `s = 0`:

```text
beta  = 1
alpha = <2,0>.
```

Then `beta | alpha` is trivial, but `alpha` cannot be a square because the
first square coordinate would require `m^2 = 2`.

## Decision

Proceed to **MG-004C — TraceOne power/Core-image landing**, with square image
as the first explicit coordinate model.  Do not introduce UFD/Euclidean
infrastructure, root-existence providers, or application-specific hypotheses.
