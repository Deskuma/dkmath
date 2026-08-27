# EUC-003 Report - Abstract Full-Cycle Division

## Goal

Turn an abstract additive division equation into kernel return and action return
without introducing real angles or Euclidean geometry.

The required data remain separate:

```text
k • step = period
F.kernel period = 1
```

## Repository facts inspected

This checkpoint builds on the generic API completed in EUC-002:

```text
KernelFamily.kernel_nsmul
UnitKernel.pow_act
KernelFamily.actLevel_add
```

`LevelSet R rho2` is the existing algebraic subtype defined by a fixed `q2`
value.  Its use here does not assume that the subtype has already been given a
Euclidean circle interpretation.

## Implementation

Added:

```text
DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean
```

The module proves the abstract return chain for a `KernelFamily T R`, an
arbitrary natural count `k`, a step, and a declared period.

Positivity is deliberately absent.  It becomes necessary only in the later
normalized `1 / k` specialization, where division by the scalar count must be
nonzero.

## Proof route

The kernel theorem rewrites the `k`th power backwards through
`KernelFamily.kernel_nsmul`, substitutes `k • step = period`, and then uses the
neutral-period hypothesis.

The ordinary action theorem rewrites action by a power through
`UnitKernel.pow_act`.  The level-set theorem first proves that finite iteration
of `actLevel t` equals `actLevel (n • t)`, then applies the same period equation.

Thus the chain is explicit:

```text
additive repetition
  -> kernel power
  -> neutral kernel
  -> identity action on every Vec
  -> identity action on every q2 level set
```

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

Both focused and aggregate builds completed on the first attempt.  The shell
printed the pre-existing `/opt/wonderful/bin/wf-env` permission warning.  Lean
emitted no warning for the new declarations.  No axiom, `sorry`, or
`native_decide` was introduced.

## New public declarations

```text
KernelFamily.kernel_pow_eq_one_of_nsmul_eq_period
KernelFamily.iterate_act_eq_act_nsmul
KernelFamily.iterate_act_eq_id_of_nsmul_eq_period
KernelFamily.iterate_actLevel_eq_actLevel_nsmul
KernelFamily.iterate_actLevel_eq_id_of_nsmul_eq_period
```

## Blocked alternatives

None.  No separate recursive kernel-power API or semantic `DkReal` transport
was needed.

## Next checkpoint

EUC-004 should define the normalized real phase family and use the existing
positive-count identity for `normalizedCycleStep k = 1 / k` as the concrete
instance of `k • step = period`.
