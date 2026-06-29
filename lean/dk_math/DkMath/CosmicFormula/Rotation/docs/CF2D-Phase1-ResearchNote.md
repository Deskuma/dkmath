# CF2D Phase 1 Research Note

## Purpose

This note summarizes the phase-1 Lean formalization of cosmic-formula
trigonometric functions.  The aim is not to redefine the analytic real
functions `sin` and `cos` directly.  The aim is to isolate an algebraic
principle from which the usual trigonometric identities and rotation formulas
arise.

The central conclusion is:

```text
Cosmic-formula cosine and sine are the core and beam coordinates of a
square-mass-preserving unit-kernel family.
```

The real functions `Real.cos` and `Real.sin` then appear as one concrete real
model of this algebraic structure.

## Algebraic State Space

The basic state is a two-component vector:

```lean
structure Vec (R : Type u) where
  core : R
  beam : R
```

The conserved square mass is:

```lean
Vec.q2 z = z.core ^ 2 + z.beam ^ 2
```

The fundamental product is:

```lean
Vec.star (a,b) (x,y) = (a*x - b*y, a*y + b*x)
```

Its key algebraic theorem is:

```lean
Vec.q2_star :
  Vec.q2 (Vec.star r z) = Vec.q2 r * Vec.q2 z
```

This theorem is a polynomial identity over an arbitrary commutative ring.  It
does not use analytic trigonometric functions, angle measures, topology, or
metric geometry.

## Unit Kernels

A unit kernel is a two-component vector of square mass one:

```lean
structure UnitKernel (R : Type u) [Semiring R] where
  val : Vec R
  q2_eq_one : Vec.q2 val = 1
```

The action of a unit kernel is the `Vec.star` product on the left:

```lean
UnitKernel.act r z = Vec.star (r : Vec R) z
```

The preservation theorem is:

```lean
UnitKernel.q2_act :
  Vec.q2 (UnitKernel.act r z) = Vec.q2 z
```

Thus rotation is read as an action preserving the square-mass level sets, not
as a primitive analytic notion.

Unit kernels are closed under the kernel product:

```lean
UnitKernel.star r s
```

and satisfy:

```lean
UnitKernel.act_star :
  UnitKernel.act (UnitKernel.star r s) z
    = UnitKernel.act r (UnitKernel.act s z)
```

This makes the kernel product the algebraic representation of action
composition.

## Conjugation And Inverses

The two-component conjugation is:

```lean
Vec.conj z = (z.core, -z.beam)
```

It preserves square mass:

```lean
Vec.q2_conj :
  Vec.q2 (Vec.conj z) = Vec.q2 z
```

and recovers the square mass into the core coordinate:

```lean
Vec.star_conj_self :
  Vec.star z (Vec.conj z) = Vec.mk (Vec.q2 z) 0

Vec.conj_star_self :
  Vec.star (Vec.conj z) z = Vec.mk (Vec.q2 z) 0
```

For unit kernels, conjugation acts as an inverse:

```lean
UnitKernel.star_conj :
  UnitKernel.star r (UnitKernel.conj r) = UnitKernel.one R

UnitKernel.conj_star :
  UnitKernel.star (UnitKernel.conj r) r = UnitKernel.one R
```

No global `Group` instance is installed in phase 1.  The inverse behavior is
recorded theorem-by-theorem.

## Kernel Families

An abstract trigonometric parameter is represented by a family of unit kernels:

```lean
structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
  kernel : T -> UnitKernel R
  map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
  map_add : forall t s,
    ((kernel (t + s) : UnitKernel R) : Vec R)
      = Vec.star ((kernel t : UnitKernel R) : Vec R)
          ((kernel s : UnitKernel R) : Vec R)
```

The wrapper theorems expose the mathematical reading:

```lean
KernelFamily.kernel_zero_one :
  F.kernel 0 = UnitKernel.one R

KernelFamily.kernel_add_star :
  F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s)
```

The target unit-kernel product is commutative, so such a family records the
commutative image of the additive parameter.  This is appropriate for the
phase-1 angle-like examples.

## Cosmic-Formula Sine And Cosine

The cosmic-formula cosine and sine are defined relative to a kernel family:

```lean
KernelFamily.cfcos F t = F.C t
KernelFamily.cfsin F t = F.S t
```

Equivalently:

```text
cfcos_F(t) = core coordinate of F(t)
cfsin_F(t) = beam coordinate of F(t)
```

They satisfy the algebraic trigonometric identities:

```lean
KernelFamily.cfcos_sq_add_cfsin_sq :
  F.cfcos t ^ 2 + F.cfsin t ^ 2 = 1

KernelFamily.cfcos_add :
  F.cfcos (t + s)
    = F.cfcos t * F.cfcos s - F.cfsin t * F.cfsin s

KernelFamily.cfsin_add :
  F.cfsin (t + s)
    = F.cfcos t * F.cfsin s + F.cfsin t * F.cfcos s

KernelFamily.cfcos_add_self :
  F.cfcos (t + t) = F.cfcos t ^ 2 - F.cfsin t ^ 2

KernelFamily.cfsin_add_self :
  F.cfsin (t + t) = 2 * F.cfcos t * F.cfsin t
```

In the additive-group layer:

```lean
KernelFamily.cfcos_neg :
  F.cfcos (-t) = F.cfcos t

KernelFamily.cfsin_neg :
  F.cfsin (-t) = -F.cfsin t

KernelFamily.cfcos_sub :
  F.cfcos (t - s)
    = F.cfcos t * F.cfcos s + F.cfsin t * F.cfsin s

KernelFamily.cfsin_sub :
  F.cfsin (t - s)
    = F.cfsin t * F.cfcos s - F.cfcos t * F.cfsin s
```

The conceptual point is that these are not postulated as analytic facts.  They
are coordinate projections of the unit-kernel law
`F.kernel (t + s) = UnitKernel.star (F.kernel t) (F.kernel s)`.

## Kernel Reconstruction And Action Formula

The final phase-1 API states that `cfcos` and `cfsin` reconstruct the unit
kernel:

```lean
KernelFamily.kernel_val_eq_mk_cfcos_cfsin :
  ((F.kernel t : UnitKernel R) : Vec R)
    = Vec.mk (F.cfcos t) (F.cfsin t)
```

Acting by this kernel gives the coordinate transformation:

```lean
KernelFamily.act_eq_cfcos_cfsin :
  UnitKernel.act (F.kernel t) z
    = Vec.mk
      (F.cfcos t * z.core - F.cfsin t * z.beam)
      (F.cfcos t * z.beam + F.cfsin t * z.core)
```

Equivalently, for `z = (x,y)`:

```text
x' = cfcos_F(t) * x - cfsin_F(t) * y
y' = cfcos_F(t) * y + cfsin_F(t) * x
```

This is the usual rotation-coordinate formula, derived without assuming the
analytic real trigonometric functions.

## Real Model

The real bridge defines the concrete family:

```lean
realTrigKernelFamily : KernelFamily Real Real
```

with kernel value:

```lean
((realTrigKernelFamily.kernel t : UnitKernel Real) : Vec Real)
  = (Real.cos t, Real.sin t)
```

The bridge theorems are:

```lean
realTrigKernelFamily_cfcos :
  realTrigKernelFamily.cfcos t = Real.cos t

realTrigKernelFamily_cfsin :
  realTrigKernelFamily.cfsin t = Real.sin t

realTrigKernelFamily_act_eq :
  UnitKernel.act (realTrigKernelFamily.kernel t) z
    = Vec.mk
      (Real.cos t * z.core - Real.sin t * z.beam)
      (Real.cos t * z.beam + Real.sin t * z.core)
```

Thus ordinary real sine and cosine are interpreted as one analytic model of the
cosmic-formula kernel-coordinate construction.

## Failure And Sign Sensitivity

The formalization also records nearby sign patterns.  The correct product

```text
(a*x - b*y, a*y + b*x)
```

preserves square mass.  The wrong plus-plus pattern

```text
(a*x + b*y, a*y + b*x)
```

leaves the residual:

```lean
Vec.q2_badStarPlus_eq_q2_mul_add_residual :
  Vec.q2 (Vec.badStarPlus r z)
    = Vec.q2 r * Vec.q2 z + 4 * r.core * r.beam * z.core * z.beam
```

The minus-minus pattern leaves the opposite residual:

```lean
Vec.q2_badStarMinus_eq_q2_mul_sub_residual :
  Vec.q2 (Vec.badStarMinus r z)
    = Vec.q2 r * Vec.q2 z - 4 * r.core * r.beam * z.core * z.beam
```

The other preserving sign pattern is explained by conjugation:

```lean
Vec.starPlusMinus_eq_star_conj_left :
  Vec.starPlusMinus r z = Vec.star (Vec.conj r) z
```

This shows that the preservation law depends on cancellation of the beam cross
terms.  A small sign error produces a measurable residual.

## Phase-1 Conclusion

Phase 1 establishes the following algebraic thesis:

```text
Trigonometric coordinate functions are the core and beam projections of a
square-mass-preserving unit-kernel family.
```

The addition formulas are coordinate expressions of kernel composition.  The
rotation formulas are coordinate expressions of kernel action.  The usual real
functions `sin` and `cos` are recovered only in the real bridge.

This gives a clean separation:

```text
Algebraic principle:
  square mass, unit kernels, kernel families, cfcos/cfsin

Real analytic model:
  Real.cos and Real.sin instantiate one such family
```

## Phase-2 Questions

The following topics are intentionally outside phase 1:

- uniqueness of the angle parameter;
- continuity and differentiability assumptions;
- normalization of angular speed;
- periodicity and the `2π` closure;
- global uniqueness of the analytic real model;
- argument, slope, gauge, and GN-ratio interpretations;
- higher-dimensional and CFBRC-oriented generalizations.

These are research directions for later layers.  The phase-1 endpoint is the
algebraic construction and formal verification of cosmic-formula sine and
cosine as unit-kernel coordinates.
