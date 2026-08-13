# IPSM-014 — Gate 4B.3 initial review and coefficient/adjoint contract

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3 review / no sign claim

## Review result

The initial `PascalCenteredXiPrimeSideQuadraticizationAudit` implementation is GREEN at its stated scope.

```text
Gate 4B.2 generic Mellin Gram kernel
  CLOSED / fixed-epsilon PSD-certified / Hermitian

RH tau=0 weight -> generic one-variable box weight
  GREEN

finite prime-mode source ledger
  GREEN

prime + archimedean + elementary + top-horizontal ledger
  GREEN

linear-source arity boundary
  GREEN

source-derived coefficient family
  OPEN

source-derived adjoint partner
  OPEN

prime-side quadraticization bridge
  OPEN
```

The module does not add a sign theorem or limit exchange.

## Weight adapter scope

`pascalCenteredXiMellinQuadraticWeight_eq_generic` exactly identifies the fixed `tau = 0` RH weight with `mellinQuadraticBoxWeight epsilon z`.

This only closes the one-variable weight adapter. It does not identify the RH source with the Hermitian Gram diagonal.

The one-variable weight is

```text
q_epsilon(z) = z^2 H_epsilon(z)
```

while the Hermitian kernel is

```text
K_epsilon(z,w) = z * conj(w) * H_epsilon(z + conj(w)).
```

## Minor API note

`pascalCenteredXiPrimeSideQuadraticizationPrimeMode` currently receives `(n _X : Nat)`, but `_X` is unused in the definition body. The cutoff is already supplied by `Finset.range (X + 1)`.

Future coefficient APIs should therefore prefer:

```text
mode data     indexed by n
cutoff data   carried by the finite index set
```

unless a later theorem genuinely uses `X` inside one mode.

## Variable firewall

Keep these roles distinct:

```text
u : Mellin-box log-average variable
t : contour-height variable
n : arithmetic von-Mangoldt mode index
```

The centered spectral coordinate in the RH weight is

```text
z_W(t) := ordinaryToCentered(rightEdge(W.sigma,t)).
```

The generic PSD feature has shape

```text
Phi(z,u) := z * exp(u*z).
```

Thus the generic node `z` is naturally instantiated on the RH right edge by the continuously varying coordinate `z_W(t)`. It is not currently identified with `n` or `log n`.

No current theorem justifies a collapse such as

```text
Gram node = prime mode n
z_j = -log n
u = t
```

or an equivalent identification.

## Stronger arity mismatch

The prime source is a one-index arithmetic sum. A finite Gram quadratic form is a two-index sum and contains off-diagonal cross terms.

There is also an index-semantics mismatch: the generic Gram node is a centered spectral coordinate, while the prime cutoff index is arithmetic.

A future bridge must first prove which family is actually paired.

## Recommended next surfaces

Before introducing an abstract provider, define the centered right-edge node and the full deoriented vertical source amplitude.

Conceptually:

```text
A_X(t)
  := primePHZFiniteUpTo X (rightEdge t)
   + archimedeanLogDeriv (rightEdge t)
   + elementaryLogDerivCorrection (rightEdge t).
```

Then prove the exact pointwise factorization

```text
deorientedVerticalIntegrand(epsilon,W,X,t)
  = mellinQuadraticBoxWeight epsilon (z_W(t)) * A_X(t).
```

The top-horizontal source remains a separate boundary surface.

Next expand the box multiplier in `u` and expose the linear two-variable source surface

```text
L_X(t,u)
  := z_W(t)^2 * exp(u*z_W(t)) * A_X(t).
```

This is still linear/bilinear source data, not a norm square.

## Coefficient/adjoint contract

A valid future provider must derive the Hermitian partner from source data. It must not merely assume that scalar excess equals a nonnegative Gram energy.

The provider must first identify one of the following, with proofs:

```text
A. arithmetic-index family
B. contour-index family
C. mixed arithmetic-contour family
```

If the natural family is contour-indexed, the existing finite `Fin N` Gram API may need a continuous/L2 extension rather than coercing contour data into prime indices.

After the index family is fixed, a valid source theorem must have a shape such as

```text
source excess
  = GramEnergy(source-derived data)
```

or

```text
source excess
  = GramEnergy(source-derived data)
    + source-derived nonnegative boundary energy.
```

Any boundary energy must be nonnegative by construction, such as a norm square, certified PSD quadratic form, or positive-measure integral.

Do not define the residual as `scalarExcess - GramEnergy` and then assume its nonnegativity.

## Whole-excess requirement

A genuine provider must eventually account for all of:

```text
vertical prime source
vertical archimedean correction
vertical elementary correction
top-horizontal correction
radial comparison
```

The radial comparison is not part of the finite arithmetic approximant itself and should remain separate until an exact completion theorem connects it to the positive form.

## Next checkpoint

```text
Gate 4B.3c0
  u / t / n index-semantics ledger
  centered right-edge node

Gate 4B.3c1
  full deoriented vertical amplitude A_X(t)
  exact factorization by q_epsilon(z_W(t))

Gate 4B.3c2
  exact box-feature expansion in u
  linear source surface L_X(t,u)

Gate 4B.3c3
  adjoint search

Gate 4B.3c4
  finite source-derived nodes/coefficients if available
  otherwise continuous Gram/L2 audit

Gate 4B.3d
  exact PSD bridge
  OR named quadraticization obstruction
```

## Stop conditions

Stop and record an obstruction if a proposed bridge requires any of the following:

```text
- a Gram node that is not source-derived
- identification of n, t, and u without a theorem
- insertion of off-diagonal terms without an exact source identity
- an assumed conjugate/adjoint factor
- dropping top-horizontal or radial terms
- a nonnegativity hypothesis carrying the desired conclusion
- zero-side energy or an equivalent vanishing theorem
- limit exchange or an infinite-height limit to justify the fixed finite identity
```

The current Gate 4B.3 result is narrower: the generic PSD structure is certified, the RH one-variable weight is adapted to it, and the remaining load-bearing task is to derive the coefficient/adjoint semantics that would turn the linear explicit-formula source into a Hermitian quadratic form.
