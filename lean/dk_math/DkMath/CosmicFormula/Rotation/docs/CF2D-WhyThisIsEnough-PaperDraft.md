# Why the CF2D Trigonometric Layer Is Enough

## Paper Draft

This note is a first paper-oriented draft extracted from the CF2D phase-1 Lean
implementation.  Its theme is:

```text
Why can such a small algebraic layer recover the usual trigonometric laws?
```

The short answer is that phase 1 does not attempt to rebuild real analysis.
It isolates the algebraic mechanism that makes two-dimensional rotation work.
Once that mechanism is stated, the trigonometric laws are no longer analytic
miracles.  They are coordinate projections of a square-mass-preserving kernel
composition law.

## Abstract

We formalize a two-component algebraic rotation kernel over an arbitrary
commutative ring.  The conserved quantity is the square mass
`x^2 + y^2`, and the fundamental product is

```text
(a,b) star (x,y) = (a*x - b*y, a*y + b*x).
```

The key theorem is the polynomial identity

```lean
Vec.q2_star :
  Vec.q2 (Vec.star r z) = Vec.q2 r * Vec.q2 z
```

From this identity we define unit kernels, their actions, and additive
families of unit kernels.  The coordinate functions of such a family are named
`cfcos` and `cfsin`.  Their Pythagorean identity, addition formulas,
double-angle formulas, negation formulas, subtraction formulas, and rotation
action formula are all obtained as algebraic consequences of the unit-kernel
law.

The usual real functions `Real.cos` and `Real.sin` enter only as one concrete
model:

```lean
realTrigKernelFamily : KernelFamily Real Real
```

For this model, Lean accepts the bridge theorems

```lean
realTrigKernelFamily_cfcos :
  realTrigKernelFamily.cfcos t = Real.cos t

realTrigKernelFamily_cfsin :
  realTrigKernelFamily.cfsin t = Real.sin t
```

by definitional equality.  This is not because real trigonometry has become
trivial.  It is because `cfcos` and `cfsin` are, by construction, the first and
second coordinates of the chosen unit-kernel family, and the real model chooses
those coordinates to be `(Real.cos t, Real.sin t)`.

## The Main Claim

The phase-1 result can be stated as follows.

```text
Trigonometric coordinate laws do not require real analysis once a
square-mass-preserving additive unit-kernel family has been supplied.
```

More explicitly:

1. The algebraic layer proves that `star` preserves square mass
    multiplicatively.
2. Unit kernels are the square-mass-one elements for this product.
3. A kernel family is an additive parameterization of unit kernels.
4. The functions `cfcos` and `cfsin` are the core and beam coordinates of the
    family.
5. The usual trigonometric identities are coordinate projections of the
    kernel-family axioms.

Thus the implementation separates two tasks that are often blended together:

```text
Algebraic task:
  explain why rotation-coordinate formulas hold.

Analytic task:
  construct or identify a particular real-valued parameterization.
```

Phase 1 completes the algebraic task and verifies that the standard real
functions instantiate it.

## Before Circles And Before Angles

The strongest reading of the current result begins before Euclidean geometry.
The primary objects are not a circle and an angle. They are a boundary
predicate and an action:

```text
q2:
  detects the conserved boundary

star:
  defines composition of kernels

act_star:
  transfers kernel composition to composition of actions

faithfulness:
  recovers the kernel from its action

first-quadrant transport:
  removes algebraic roots outside the semantic boundary
```

This order matters. The statement proved for the distinguished boundary
kernel is:

```text
the q2-preserving action has exact order four
```

It is not initially:

```text
the action is a 90-degree rotation of a circle
```

The latter sentence contains additional information not present in the
algebraic definitions. Reading `q2(x,y) = x^2 + y^2` as squared Euclidean
radius requires a choice of a Euclidean plane, equally scaled orthogonal axes,
and the usual geometric interpretation of its level sets. Reading exact order
four as 90 degrees additionally requires a notion of angle, a full turn, and a
degree convention.

None of those choices is used in the Lean proof. What Lean establishes first
is a composable boundary-preserving mechanism with four-step return and no
earlier positive return. Once the standard Euclidean model is supplied, the
same mechanism is recognized as a quarter-turn. Geometry does not generate
the algebraic behavior here; geometry is a later interpretation in which the
already-proved behavior has a familiar name.

This gives a more precise explanation of the construction's strength:

```text
the preservation law locates the motion;
the product law generates the motion;
the action law realizes the motion;
faithfulness makes the realization exact;
the semantic boundary selects the admissible roots.
```

The usual circle and trigonometric descriptions are therefore models of this
earlier algebraic structure.

The pointwise orbit makes the distinction concrete:

```text
(x,y) -> (-y,x) -> (-x,-y) -> (y,-x) -> (x,y).
```

For a nonzero state this orbit has minimal period four. The zero state remains
fixed. Thus exact order four of the action is a global function statement; it
does not assert that every state has the same point period. Neither statement
requires a circle or an angle. Those concepts explain the orbit after a
Euclidean model is chosen.

## Compass, Pin, String, And Pen

The construction has a classical geometric analogy.

One does not need to solve real analysis in order to draw a circle.  A compass
is enough.  A pin, a string, and a pen are also enough.  These devices enforce
a constraint: the distance from the center remains fixed.

The CF2D implementation does the formal analogue. Instead of first building
all analytic properties of `sin` and `cos`, it installs an algebraic device:

```text
square mass:
  x^2 + y^2

unit kernel:
  a^2 + b^2 = 1

action:
  (x,y) |-> (a*x - b*y, a*y + b*x)
```

The theorem `UnitKernel.q2_act` says that this device keeps the square mass
fixed. This is the Lean version of "the string length remains fixed." More
precisely, the theorem first gives invariant level sets. Calling those level
sets circles is justified only after the standard Euclidean interpretation is
chosen.

This analogy also explains why the code is short.  The implementation is not
simulating motion point-by-point.  It specifies the preserving mechanism.

## Why `rfl` Appears In The Real Bridge

The real bridge is deliberately simple:

```lean
noncomputable def realTrigKernelFamily : KernelFamily Real Real where
  kernel t :=
    { val := ⟨Real.cos t, Real.sin t⟩
      q2_eq_one := by
        simp [Vec.q2, Real.cos_sq_add_sin_sq t] }
  map_zero := by
    simp [Vec.one]
  map_add := by
    intro t s
    simp [Vec.star, Real.cos_add, Real.sin_add]
    ring
```

The analytic work needed from Mathlib is concentrated here:

- `Real.cos_sq_add_sin_sq`;
- `Real.cos_add`;
- `Real.sin_add`;
- the zero values of `cos` and `sin`, discharged by simplification.

After the model is constructed, the coordinate bridge is definitional:

```lean
theorem realTrigKernelFamily_cfcos (t : Real) :
    realTrigKernelFamily.cfcos t = Real.cos t := rfl

theorem realTrigKernelFamily_cfsin (t : Real) :
    realTrigKernelFamily.cfsin t = Real.sin t := rfl
```

This is a useful Lean design point.  The abstraction is not an extra theorem
layer fighting the real API.  It is a coordinate projection abstraction whose
real instance projects definitionally to Mathlib's existing functions.

The `rfl` result should be read precisely:

```text
For the real model, the CF2D coordinate named cfcos is definitionally the
first coordinate, and that first coordinate was defined to be Real.cos.
```

It should not be read as:

```text
All analytic facts about Real.cos and Real.sin are proved by rfl.
```

The analytic facts are used to prove that `(Real.cos t, Real.sin t)` is a valid
unit-kernel family.  Once that proof is available, the algebraic API handles
the coordinate laws uniformly.

## Why This Is A Lean-Friendly Construction

The construction fits Lean well for several reasons.

First, the core identity is a polynomial identity over a commutative ring:

```lean
Vec.q2_star
```

This is exactly the kind of statement Lean can verify robustly with algebraic
normalization.

Second, the geometric language is introduced only after the invariant is
proved.  The code does not need to define an angle, an arc length, a topology,
or a differentiable structure in order to state the rotation action.

Third, the abstraction boundary is explicit.  `KernelFamily` is the interface:

```lean
kernel : T -> UnitKernel R
map_zero : kernel 0 = one
map_add : kernel (t + s) = kernel t star kernel s
```

Every trigonometric formula in phase 1 is downstream of this interface.  This
gives the formalization a small trusted mathematical surface.

Fourth, the real model is not duplicated.  Mathlib remains the source of the
standard real trigonometric functions.  CF2D contributes a structural
explanation of why their rotation formulas are instances of a more general
algebraic mechanism.

## Sign Sensitivity

The implementation also records nearby sign patterns.  This is important for a
research presentation because it shows that the chosen kernel is not arbitrary.

The correct sign pattern is:

```text
(a*x - b*y, a*y + b*x)
```

Changing signs can leave a residual:

```lean
Vec.q2_badStarPlus_eq_q2_mul_add_residual :
  Vec.q2 (Vec.badStarPlus r z)
    = Vec.q2 r * Vec.q2 z + 4 * r.core * r.beam * z.core * z.beam

Vec.q2_badStarMinus_eq_q2_mul_sub_residual :
  Vec.q2 (Vec.badStarMinus r z)
    = Vec.q2 r * Vec.q2 z - 4 * r.core * r.beam * z.core * z.beam
```

The remaining preserving sign pattern is explained by conjugation:

```lean
Vec.starPlusMinus_eq_star_conj_left :
  Vec.starPlusMinus r z = Vec.star (Vec.conj r) z
```

Thus the formalization does not merely show that one formula works.  It also
identifies the cancellation that makes it work and the residuals that appear
when the cancellation is broken.

## What Phase 1 Does Not Claim

The result is intentionally not a uniqueness theorem for analytic real sine
and cosine.

Phase 1 proves:

```text
Any additive family of square-mass-one kernels has coordinate functions
satisfying the trigonometric algebraic laws.
```

It does not yet prove:

- continuity;
- differentiability;
- angular-speed normalization;
- periodicity;
- uniqueness of the real analytic model;
- the `2*pi` closure;
- global reconstruction of angle from a point on a level set.

Those belong to later analytic or geometric layers.  This limitation is a
strength of the phase-1 result: the algebraic source of the formulas is cleanly
separated from analytic uniqueness.

## Possible Paper Structure

An initial paper can be organized as follows.

1. Introduction: why trigonometric formulas can be studied through invariants.
2. The two-component square-mass algebra.
3. Unit kernels and square-mass-preserving actions.
4. Kernel families and coordinate trigonometric functions.
5. Lean implementation and theorem inventory.
6. The real model and the meaning of definitional equality.
7. Sign sensitivity and failure residuals.
8. Limitations and future analytic layers.

The paper's central contribution should not be described as replacing
Mathlib's real trigonometric functions.  A better description is:

```text
We formalize a minimal algebraic interface whose coordinate projections satisfy
the standard trigonometric identities, and we show that Mathlib's real sine and
cosine instantiate this interface definitionally at the coordinate level.
```

## Working Title Options

- Why This Is Enough: A Lean Formalization of Trigonometry from Square-Mass
  Preserving Kernels
- Trigonometric Laws as Coordinate Projections of Unit-Kernel Composition
- A Minimal Algebraic Interface for Two-Dimensional Rotation in Lean
- From Compass Invariants to Lean Kernels: A Formal Account of CF2D

## Current Research Value

The current implementation is research-presentable because it demonstrates a
small but meaningful separation:

```text
Real analysis explains that the standard real functions form a valid model.
CF2D explains why any valid model has the trigonometric coordinate laws.
```

This is the reason the code can be simple while remaining mathematically
substantial.  It does not avoid the hard analytic theory.  It places that
theory at the boundary where it belongs, and proves the rotation algebra once
for every model satisfying the boundary conditions.
