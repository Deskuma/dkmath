# EUC-004 Report - Normalized Real Cycle Division

## Goal

Connect the existing normalized scalar step `1 / k` to the real CF2D kernel
family and prove positive-count kernel and action return.

This checkpoint adopts Convention A:

```text
normalized phase p
  -> real angle p * (2 * Real.pi)
```

Thus normalized phase `1` is one full real trigonometric cycle.

## Repository facts inspected

The concrete bridge reuses:

```text
realTrigKernelFamily
DkMath.Analysis.DkNNRealQ.normalizedCycleStep
DkMath.Analysis.DkNNRealQ.normalizedCycleStep_mul_returnCount
KernelFamily.kernel_nsmul
UnitKernel.pow_act
```

The existing normalized scalar definitions remain in their original module and
namespace.  They were neither copied nor moved.

## Implementation

Extended:

```text
DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean
```

The module now packages the reparameterized real family, the one-step regular
kernel, kernel return, ordinary action return, and return on every real `q2`
level set.

The `k = 0` expression remains a field-defined scalar but receives no cycle
interpretation.  Every public regular-return theorem requires `0 < k`.

## Proof route

The real normalized family inherits addition from `realTrigKernelFamily`
through distributivity of multiplication by `2 * Real.pi`.  Its kernel at
phase `1` is neutral by `Real.cos_two_pi` and `Real.sin_two_pi`.

The central proof keeps the intended chain visible:

```text
normalizedCycleStep_mul_returnCount
  -> k • regularPhaseStep k = 1
  -> KernelFamily.kernel_nsmul
  -> normalizedRealKernelFamily.kernel 1 = 1
  -> regularKernel k ^ k = 1
```

`UnitKernel.pow_act` then gives identity action on every state.  Subtype
extensionality transports the same result to every real square-mass level set.

The theorem proves return after `k` products.  It does not yet claim that `k`
is the least positive return count.

## Build command and result

From `lean/dk_math`:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

The first focused elaboration showed that iterating `LevelSet.act` does not
definitionally reduce to iterating the underlying `Vec` action.  The final
proof therefore reuses the abstract EUC-003 level-set return theorem, which is
the stronger and more stable route.

The build replayed two pre-existing `ring_nf` suggestions from
`CosmicFormulaDim.lean` and the shell's existing `/opt/wonderful/bin/wf-env`
permission warning.  Lean emitted no warning for the declarations added here.
No axiom, `sorry`, or `native_decide` was introduced.

## New public declarations

```text
normalizedPhaseAngle
normalizedRealKernelFamily
regularPhaseStep
regularKernel
normalizedRealKernelFamily_kernel_one
regularPhaseStep_nsmul_eq_one
regularKernel_pow_eq_one
regularKernel_iterate_act_eq_id
regularKernel_iterate_actLevel_eq_id
```

## Blocked alternatives

Convention B, defining the step directly as `2 * Real.pi / k`, was not chosen.
It would obscure the existing normalized scalar return theorem and duplicate
its division argument.

No trigonometric tactic was used to prove the `k`-fold return directly.  The
trigonometric API appears only in the one-full-cycle neutral-kernel lemma.

## Next checkpoint

EUC-005 should define the generic `ExactKernelOrder` predicate and investigate
the smallest stable pinned-Mathlib route from the real regular kernel to
minimal positive return.  The return theorem proved here must remain separate
from that minimality argument.
