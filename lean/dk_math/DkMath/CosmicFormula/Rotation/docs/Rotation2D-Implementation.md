# Cosmic Formula Rotation 2D Implementation

## Location

The implementation is under:

- `DkMath.CosmicFormula.Rotation`
- `DkMath.CosmicFormula.Rotation.CF2D`
- `DkMath.CosmicFormula.Rotation.CF2D.Basic`
- `DkMath.CosmicFormula.Rotation.CF2D.Trig`
- `DkMath.CosmicFormula.Rotation.CF2D.Real`

The physical directory is `DkMath/CosmicFormula/Rotation/CF2D`.  The `CF2D`
name avoids Lean's escaped-identifier syntax while keeping the public module
name compact.

## Algebraic Core

`Basic.lean` introduces a two-component state:

```lean
structure Vec (R : Type u) where
  core : R
  beam : R
```

The square mass is:

```lean
Vec.q2 z = z.core ^ 2 + z.beam ^ 2
```

The unit-kernel product is:

```lean
Vec.star (a,b) (x,y) = (a*x - b*y, a*y + b*x)
```

The central theorem is:

```lean
Vec.q2_star :
  Vec.q2 (Vec.star r z) = Vec.q2 r * Vec.q2 z
```

This is proved by polynomial expansion with `ring`, over an arbitrary
commutative ring.  No trigonometric functions, circle facts, angle facts, or
metric-space facts are used.

## Unit Kernels and Rotation Reading

`UnitKernel R` packages a vector whose square mass is `1`:

```lean
structure UnitKernel (R : Type u) [Semiring R] where
  val : Vec R
  q2_eq_one : Vec.q2 val = 1
```

Its action is:

```lean
UnitKernel.act r z = Vec.star r.val z
```

The preservation theorem is:

```lean
UnitKernel.q2_act :
  Vec.q2 (UnitKernel.act r z) = Vec.q2 z
```

Thus a "rotation" is not assumed first.  The formal layer finds a
square-mass-preserving unit-kernel action, and this action receives the
rotation interpretation.

## Level Sets

`LevelSet R rho2` is the square-mass level set `Vec.q2 z = rho2`.
`LevelSet.act` proves that every unit-kernel action stays inside every level
set.  This is the algebraic counterpart of defining a circle as a level set of
the conserved square mass.

## Coordinate Functions

`Trig.lean` defines an abstract additive-monoid family of unit kernels:

```lean
structure KernelFamily (T : Type u) (R : Type v) [AddMonoid T] [CommRing R] where
  kernel : T -> UnitKernel R
  map_zero : ((kernel 0 : UnitKernel R) : Vec R) = Vec.one R
  map_add : forall t s,
    ((kernel (t + s) : UnitKernel R) : Vec R)
      = Vec.star ((kernel t : UnitKernel R) : Vec R)
          ((kernel s : UnitKernel R) : Vec R)
```

The coordinate functions are:

```lean
KernelFamily.C F t
KernelFamily.S F t
```

The formal identities are:

```lean
KernelFamily.C_sq_add_S_sq :
  F.C t ^ 2 + F.S t ^ 2 = 1

KernelFamily.C_zero :
  F.C 0 = 1

KernelFamily.S_zero :
  F.S 0 = 0

KernelFamily.C_add_zero :
  F.C (t + 0) = F.C t

KernelFamily.S_add_zero :
  F.S (t + 0) = F.S t

KernelFamily.C_zero_add :
  F.C (0 + t) = F.C t

KernelFamily.S_zero_add :
  F.S (0 + t) = F.S t

KernelFamily.act_zero :
  UnitKernel.act (F.kernel 0) z = z

KernelFamily.C_add :
  F.C (t + s) = F.C t * F.C s - F.S t * F.S s

KernelFamily.S_add :
  F.S (t + s) = F.C t * F.S s + F.S t * F.C s

KernelFamily.act_add :
  UnitKernel.act (F.kernel (t + s)) z
    = UnitKernel.act (F.kernel t) (UnitKernel.act (F.kernel s) z)

KernelFamily.C_add_self :
  F.C (t + t) = F.C t ^ 2 - F.S t ^ 2

KernelFamily.S_add_self :
  F.S (t + t) = 2 * F.C t * F.S t
```

These are the cosmic-formula versions of the basic trigonometric identities:
they are derived from conservation and kernel composition, not from existing
trigonometric API.

## Additive Group Layer

When the parameter type has an additive group structure, `Trig.lean` also
derives the negative-parameter and subtraction formulas:

```lean
KernelFamily.kernel_add_neg :
  Vec.star (F.kernel t) (F.kernel (-t)) = Vec.one R

KernelFamily.C_neg :
  F.C (-t) = F.C t

KernelFamily.S_neg :
  F.S (-t) = -F.S t

KernelFamily.C_sub :
  F.C (t - s) = F.C t * F.C s + F.S t * F.S s

KernelFamily.S_sub :
  F.S (t - s) = F.S t * F.C s - F.C t * F.S s
```

The proofs are still algebraic: they use the unit square-mass identity and the
fact that `R(t) ⋆ R(-t)` is the neutral kernel.

## Real Bridge

`Real.lean` is the compatibility layer with the usual real trigonometric
functions.  It defines:

```lean
realTrigKernelFamily : KernelFamily ℝ ℝ
```

with kernel value `(Real.cos t, Real.sin t)`, using the standard real theorems
only in this bridge layer.  The coordinate projections are exposed as:

```lean
realTrigKernelFamily_C :
  realTrigKernelFamily.C t = Real.cos t

realTrigKernelFamily_S :
  realTrigKernelFamily.S t = Real.sin t
```

## Extension Notes

The implementation is deliberately algebraic and ring-polymorphic.  This keeps
the 2D kernel reusable for later CFBRC, complex-like, 3D, or finite-dimensional
geometric layers.  Analytic assumptions such as continuity of the parameter
family are left out of the algebraic layer and can be added in separate bridge
modules.
