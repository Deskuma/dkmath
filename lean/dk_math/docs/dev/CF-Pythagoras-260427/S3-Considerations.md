# S3 Considerations

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89

S3 should begin from the Chapter 2 boundary, not from the beginning of the
Pythagorean route.  Chapter 2 leaves a clean ordinary cubic engine; S3 should
choose how to extend or feed that engine.

## Starting Point

The stable Chapter 2 entry point is:

```lean
DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext
```

The stable contradiction endpoints are:

```lean
C.val_le_one_contradiction
C.squarefree_contradiction
```

Thus S3 should focus on one of two roles:

```text
produce a context
produce GN fuel
```

or on a deliberately separate exceptional route.

## Option A: Exceptional Cubic Branch

Goal:

```text
Handle q = 3 separately from the ordinary branch.
```

Likely first artifact:

```lean
structure CubicExceptionalFLTContext where
  q : Nat
  a : Nat
  b : Nat
  y : Int
  ...
  hq_eq_three : q = 3
```

This should not reuse the ordinary contradiction theorem blindly, because that
route depends on `q ∤ 3`.  The first S3 task would be to identify the replacement
local obstruction for the prime dividing the degree.

Risk:

```text
This may require new number-theoretic content, not just API plumbing.
```

## Option B: GN Fuel Automation

Goal:

```text
Automatically derive the valuation or squarefree fuel consumed by
CubicPrimitiveFLTContext.
```

Candidate target theorems:

```lean
theorem CubicPrimitiveFLTContext.gn_val_le_one ...
theorem CubicPrimitiveFLTContext.gn_squarefree ...
```

or external fuel providers:

```lean
theorem primitive_cubic_GN_val_le_one ...
theorem primitive_cubic_GN_squarefree ...
```

This direction should inspect and promote the existing Zsigmondy /
cyclotomic / squarefree research layer.  It is probably the most direct route
to making the Chapter 2 engine fire automatically.

Risk:

```text
Existing research files still contain a known `sorry`; promotion must separate
proved API from exploratory API.
```

## Option C: General Degree Bridge

Goal:

```text
Lift the cubic-specific route into a degree-parametric bridge where possible.
```

This should preserve the cubic API.  The point is not to erase
`CubicPrimitiveFLTContext`, but to identify which theorem families are truly
degree-generic and which branches are degree-specific.

Possible artifacts:

```lean
structure PrimitiveFLTContext (d : Nat) where ...
theorem primitive_GN_val_le_one_contradiction ...
```

Risk:

```text
Over-generalization may obscure the clean cubic route and delay the q = 3 or
GN fuel work.
```

## Option D: d = 4 / Pythagorean Square-Lift Route

Goal:

```text
Use the Pythagorean square-lift viewpoint to study the fourth-power obstruction.
```

This is conceptually close to the original Pythagorean motivation:

```text
a^2 + b^2 = c^2
a = u^2, b = v^2, c = w^2
=> u^4 + v^4 = w^4
```

The route may connect to classical descent more naturally than to the cubic
primitive-prime engine.  It should be treated as its own branch.

Risk:

```text
The proof shape may be descent-heavy rather than valuation-heavy.
```

## Recommended S3 Opening

The most conservative S3 opening is:

```text
S3-A: isolate the q = 3 exceptional branch as a context and prove only the
API boundary first.
```

The most productive S3 opening, if the goal is to make the existing engine fire,
is:

```text
S3-B: inspect Zsigmondy / squarefree APIs and promote a proved GN fuel provider.
```

The recommended order is:

1. S3-A: create the exceptional-branch boundary document or context skeleton
2. S3-B: promote GN fuel providers from proved APIs only
3. S3-C: revisit general degree abstraction after the cubic branch boundaries
   are stable

## S3 Non-Goals

S3 should avoid these at the start:

- claiming full FLT `d = 3` closure before `q = 3` is handled
- importing research-warning-heavy modules into the lightweight GN bridge
- replacing the clean cubic context with a broad abstraction before it has
  downstream users
- mixing the `d = 4` square-lift route into the cubic primitive route
