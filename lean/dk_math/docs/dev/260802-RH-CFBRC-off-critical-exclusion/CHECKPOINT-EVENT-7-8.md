# RH–CFBRC Checkpoint — Finite Closure and Standard Zeta Target

Date: 2026-08-02

Branch:

```text
wip/RH-CFBRC-off-critical-exclusion-260802-v0
```

PR: #76

## 1. Public-build discipline

Every module in this checkpoint is re-exported from:

```text
DkMath.RH
```

A successful CI result therefore means that the new module is reachable from
the public import graph and was checked by the full `lake build`. A green build
for an isolated, unimported file is not accepted as evidence.

## 2. Event 7A — finite complex closure

Module:

```text
DkMath.RH.CFBRC.FiniteClosure
```

For a finite complex-vector family, define:

- its endpoint;
- a common observation rotation;
- positive real-axis projected mass;
- absolute negative real-axis projected mass;
- transverse imaginary gap.

Lean proves:

$$
\operatorname{endpoint}=0
\quad\Longleftrightarrow\quad
M_+=M_-
\;\land\;
Q=0,
$$

under every nonzero common rotation.

This is the exact finite decomposition of complex closure into longitudinal
mass balance and transverse-gap disappearance.

CI: success through `DkMath.RH`.

## 3. Event 7B — path ordering and historical control model

Module:

```text
DkMath.RH.CFBRC.FiniteClosurePermutation
```

Lean proves:

- `List.Perm` preserves the endpoint;
- reversal preserves the endpoint;
- negating every vector negates the endpoint;
- appending the negated reversed copy closes by construction.

The historical Python construction is named:

```lean
forcedReverseClosure
```

and is explicitly documented as a control model rather than an analytic zero
detector. Sorting or changing the drawing order may change the visible path but
cannot change the finite endpoint.

CI: success through `DkMath.RH`.

## 4. Event 7C — normalized CFBRC mass coordinates

Module:

```text
DkMath.RH.CFBRC.FiniteMassNormalization
```

For nonzero total projected mass, define:

$$
x=\frac{M_+}{M_++M_-},
\qquad
u=\frac{M_-}{M_++M_-}.
$$

Lean proves:

$$
x+u=1,
$$

$$
\operatorname{Big}=(x+u)^2=1,
$$

and, at finite closure,

$$
x=u=\frac12,
\qquad
x-u=0.
$$

Thus the CFBRC `Big` is preserved while closure is represented by center-offset
zero.

CI: success through `DkMath.RH`.

## 5. Event 7D — centered finite bridge

Module:

```text
DkMath.RH.CFBRC.FiniteCenteredBridge
```

The remaining center-identification obligation is isolated as

$$
\sigma-\frac12
=
\operatorname{normalizedProjectedCenterOffset}.
$$

Given this identification and a genuine finite closure, Lean derives:

$$
\sigma=\frac12
$$

and hence a zero of every positive-degree standard CFBRC projection.

The reusable interface is:

```lean
FiniteCenteredZeroBridge ι Zero
```

Its load-bearing fields are:

- a genuine endpoint realization;
- nonzero observation rotation;
- nonzero projected mass total;
- endpoint closure;
- center identification.

CI: success through `DkMath.RH`.

## 6. Event 7E — genuine finite Dirichlet-eta model

Module:

```text
DkMath.RH.CFBRC.EtaFiniteClosure
```

Define the zero-based eta vectors by

$$
v_m(s)=(-1)^m(m+1)^{-s}.
$$

Lean separates the genuine alternating sum into its two parity blocks:

$$
\eta_N(s)=A_N(s)-B_N(s),
$$

and proves:

$$
\eta_N(s)=0
\quad\Longleftrightarrow\quad
A_N(s)=B_N(s).
$$

The generic finite mass-gap and normalized-half theorems specialize directly
to this eta family. This is analytically distinct from `forcedReverseClosure`.

CI: success through `DkMath.RH`.

## 7. Event 8A — Mathlib standard-zeta target

Module:

```text
DkMath.RH.CFBRC.StandardZetaBridge
```

The module imports Mathlib's standard:

- `riemannZeta`;
- `RiemannHypothesis`;
- `riemannZetaZeros` API.

It defines `NontrivialRiemannZetaZero` to match Mathlib's official RH statement
and proves the exact equivalence between that local predicate and
`RiemannHypothesis`.

Two sufficient interfaces are now kernel-checked:

```lean
StandardZetaToCFBRCBridge
StandardZetaFiniteCenteredBridge ι
```

Lean proves:

```lean
riemannHypothesis_of_standardZetaToCFBRCBridge
riemannHypothesis_of_standardZetaFiniteCenteredBridge
riemannHypothesis_of_standardZeta_map_zero
```

Therefore the final positive-degree direct obligation is precisely:

```lean
∀ {s : ℂ}, NontrivialRiemannZetaZero s →
  offCriticalCFBRC d s.re (phase s) = 0
```

No theorem in this checkpoint claims that this obligation has been solved.

CI: success through `DkMath.RH`.

## 8. Mathlib audit boundary

Mathlib v4.32.2 provides:

- the analytically continued `riemannZeta`;
- completed zeta and its functional equation;
- the formal `RiemannHypothesis` proposition;
- the Dirichlet-series identity only in the half-plane `1 < re s`;
- discreteness of the standard zeta-zero set.

Consequently, the critical-strip bridge cannot identify raw Dirichlet partial
sums with `riemannZeta`. It must use a genuine convergent/regularized expression,
a completed-zeta representation, or a separately proved eta continuation
identity.

## 9. Current boundary

The algebraic receiving side is complete. The next research obligation is not
to prove another consequence of closure, but to construct one of the following
without circular use of `re s = 1/2`:

1. a standard-zeta `map_zero` into the standard CFBRC zero locus;
2. a standard-zeta finite/regularized centered realization;
3. a convergent eta or completed-zeta limit whose center identification equals
   `s.re - 1/2`.

Prime-factor allocation remains an interpretation layer after the location
theorem and is not required by the current RH proof kernel.
