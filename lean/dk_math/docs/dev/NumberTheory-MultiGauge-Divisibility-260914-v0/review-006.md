# Review 006 — MG-004A Eisenstein lattice landing

## Verdict

**APPROVED — Outcome A: LATTICE LANDING IFF ESTABLISHED**

MG-004A correctly implements the concrete Eisenstein receiver layer requested by
`instruction-006.md`. No repair checkpoint is required before MG-004B.

## What is now production-proved

The new module

```text
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
```

reuses the existing `TraceOneInt (-1)` carrier and proves the exact standard
Eisenstein criterion

```text
beta | alpha
<->
norm beta | (alpha * conj beta).first-coordinate
and
norm beta | (alpha * conj beta).second-coordinate
```

under the concrete nonzero-beta hypothesis, discharged through the
positive-definite `s = -1` norm.

The explicit coordinate formulas are consistent with the existing
`eisensteinCoord` convention:

```text
alpha = a + b omega
beta  = c + d omega

alpha * conj beta
  = (a*c - a*d + b*d)
    + (b*c - a*d) omega.
```

The converse reconstructs an integral quotient from the two coordinate
divisibility witnesses and cancels the conjugate denominator. This is a real
lattice-landing theorem, not merely a norm consequence.

## Norm-only firewall

The theorem

```text
eisenstein_dvd_imp_norm_dvd_norm
```

correctly records norm divisibility as necessary only.

The regression

```text
alpha = eisensteinCoord (-1) 2
beta  = eisensteinCoord (-2) 1
```

has

```text
norm alpha = norm beta = 7
alpha * conj beta = eisensteinCoord 5 (-3)
```

so norm divisibility holds while coordinate landing fails. This is the desired
kernel-checked witness that scalar-volume compatibility does not imply lattice
landing.

## Generalization boundary

MG-004A uses a fact special to the positive-definite `s = -1` order:

```text
norm x = 0 <-> x = 0.
```

This must **not** be generalized blindly to arbitrary `TraceOneInt s`.
For example, at `s = 0`, the nonzero element `tau 0` has norm zero.

The general theorem should instead assume directly

```text
norm beta != 0
```

and prove cancellation from the coordinate multiplication matrix. If
`z = (c,d)`, multiplication by `z` has matrix determinant

```text
c^2 + c*d - s*d^2 = norm z.
```

Hence nonzero norm is enough for injectivity over the integer coordinate
lattice, without any positive-definite zero-fiber theorem.

## MG-004B recommendation

Proceed to a neutral generic module, preferably

```text
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
```

with the parameter `s : Z` left arbitrary.

Primary target:

```text
norm beta != 0
->
(beta | alpha
  <->
  norm beta | (alpha * conj beta).fst
  and
  norm beta | (alpha * conj beta).snd)
```

Then expose the coordinate polynomial specialization

```text
alpha = (a,b)
beta  = (c,d)

(alpha * conj beta).fst = a*c + a*d - s*b*d
(alpha * conj beta).snd = b*c - a*d
norm beta               = c^2 + c*d - s*d^2.
```

The Eisenstein theorem should remain API-compatible and may be refactored to
use the generic result only if this reduces duplication without destabilizing
the already-approved concrete module.

## Scope guard

MG-004B should not yet add:

- MultiGauge application assumptions;
- ABC / FLT / Petal imports;
- power/Core-image landing;
- Euclidean-domain or UFD infrastructure;
- a false general theorem `norm x = 0 <-> x = 0`.

The receiver layer remains neutral arithmetic infrastructure.
