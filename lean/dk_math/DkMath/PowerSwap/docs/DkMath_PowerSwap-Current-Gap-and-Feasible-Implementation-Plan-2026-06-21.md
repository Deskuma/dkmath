# DkMath.PowerSwap Current Gap and Feasible Implementation Plan

Date: 2026-06-21

## 1. Purpose

This report compares the current `DkMath.PowerSwap` implementation with
`DkMath_PowerSwap-Implementation-Plan-and-Design.md`, investigates decidable
comparison, and replaces the old stage order with an implementation plan that
can be executed against the present workspace.

The central conclusion is:

```text
PowerSwap can normalize and transport power expressions.
It cannot by itself make asymptotic DkNNRealQ order decidable.
```

The practical comparison layer should therefore distinguish:

```text
finite structural comparison       decidable
finite interval observation        decidable
proof-carrying strict comparison    constructive
full DkNNRealQ comparison           total as a proposition, not decidable
```

### Type-name policy

This plan intentionally uses both existing types; they are not aliases:

```text
DkNNReal:
  a nonnegative interval representative;
  finite endpoint inspection and executable bounded search live here.

DkNNRealQ:
  the quotient of representatives;
  public equality, order, semiring operations, and frame evaluation live here.
```

Every observation theorem must connect its representative result to quotient
order through `DkNNRealQ.mk`. A future rename is outside this plan.

## 2. Current implementation

The public entry point `DkMath.PowerSwap` imports five modules.

| Module | Current responsibility | Status |
| --- | --- | --- |
| `Basic` | Natural-number relation `a ^ b = b ^ a` and small examples | Implemented |
| `Exchange` | Rewrites `(a ^ t) ^ m` to `a ^ (t * m)` over `Nat` and `Int` | Implemented |
| `NormalForm` | `PowNormalForm`, evaluation, exponent scaling, same-base multiplication | Implemented |
| `Branch` | Real `rpow` parametrization, correctness, and convergence to `(e,e)` | Implemented |
| `Contours` | Real logarithmic coordinates, hyperbolic form, and local model | Implemented |

`DkMath.FLT.PowerSwapBridge` exists, but is currently only a placeholder.
There is no `DkNNRealQ` PowerSwap bridge.

## 3. Agreement with the original design

The following design intentions have been realized.

1. PowerSwap is an independent top-level package.
2. The discrete equation `a ^ b = b ^ a` is formalized.
3. Exponent exchange is available as an exact algebraic theorem.
4. A witness-based normal form exists:
   `HasPowNormalForm n` stores a form and an evaluation proof.
5. The analytic branch and the center `(e,e)` have been formalized.
6. Logarithmic contour coordinates are isolated from arithmetic consumers.

`HasPowNormalForm` already embodies the original recommendation to prefer a
normalization witness over an unrestricted root-producing normalization
function.

## 4. Differences from the original design

### 4.1 The generic structural core is missing

The planned objects below do not exist:

```text
PowerFrame
NatPowerFrame
PowerSwapRel on frames
swap on frames
LevelFunction
SameLevel
NormalNatPowerFrame
NormalizesTo
SameDegreeComparison
CosmicPowerFrame
SameCosmicDegreeComparison
```

The current `PowNormalForm` is specialized to `Nat`. This is useful and
computable, but it is not the type-independent core described by the design.

### 4.2 File responsibilities diverged

The design proposed `Core`, `Swap`, `Level`, `Normalize`, `Compare`, and
`CosmicFrame`. The current package instead grew from an earlier LPS
refactoring into:

```text
Basic / Exchange / NormalForm / Branch / Contours
```

This is not merely a naming difference. The analytic layer was implemented
before the abstract comparison and bridge layers.

### 4.3 The core/analytic dependency boundary is weaker than planned

`Branch` and `Contours` import all of Mathlib and use `Real.log`, `Real.exp`,
`Real.rpow`, derivatives, and filters. The top-level `DkMath.PowerSwap`
re-exports these analytic modules.

The structural modules remain usable independently, but importing the public
entry point is no longer a lightweight core import.

### 4.4 Same-degree comparison is missing

There is no API turning:

```text
same degree + ordered bases
```

into an order between evaluated frames. This is the most important missing
step before a `DkNNRealQ` bridge.

### 4.5 Cosmic decomposition is missing

No PowerSwap structure currently records:

```text
base = Core + Gap
value = (Core + Gap) ^ degree
```

The existing DkReal canonical order can extract the additive Gap, but this has
not yet been connected to PowerSwap frames.

## 5. Decidable comparison investigation

### 5.1 What is already decidable

`PowNormalForm` derives `DecidableEq`. Its fields are natural numbers, so the
following are computable:

```text
syntactic equality of normal forms
base comparison
exponent comparison
evaluation into Nat
comparison of evaluated Nat values
```

Evaluation comparison is mathematically exact but may create very large
natural numbers. It is not a canonical factorization or normalization
algorithm.

### 5.2 What is not decidable

`DkNNRealQ` currently provides:

```text
PartialOrder
Std.Total (· <= ·)
IsOrderedRing
IsStrictOrderedRing
CanonicallyOrderedAdd
```

It intentionally does not provide `DecidableEq`, `DecidableLE`, or
`LinearOrder`. Mathlib's `LinearOrder` requires decidable equality and
decidable order.

The order is defined by convergence of rational interval defects. Totality
proves that one orientation exists, but does not provide a terminating
algorithm that chooses it.

PowerSwap does not remove this obstruction. A successful normalization to a
common degree still leaves a comparison of `DkNNRealQ` bases.

### 5.3 Finite strict comparison is observable

For representatives, strict order has a finite certificate:

```text
x < y
iff
exists n, x.interval(n).hi < y.interval(n).lo
```

At any fixed stage, the three-way observation is decidable:

```text
left-separated
overlapping
right-separated
```

Searching stages can therefore semi-decide strict inequality. It may not
terminate when the quotient values are equal, because overlap at every finite
stage is not itself a finite equality certificate.

### 5.4 Recommended policy

Do not install global classical `DecidableLE` or `LinearOrder` instances.

Instead provide three explicit APIs:

```text
StageComparison       -- decidable result at one finite stage
compareUpTo fuel      -- bounded, terminating observation
StrictCertificate     -- proof-carrying successful separation
```

Clients needing noncomputable case analysis may use `Classical` locally.
Clients needing executable comparison must work with bounded observations or
with a domain carrying stronger certificates.

## 6. Feasible implementation plan

### Phase 0: Reconfirm the live workspace

Before each implementation phase, verify the current names rather than relying
on this document alone:

```text
DkNNReal and DkNNRealQ definitions and namespaces
DkMath.Analysis.DkReal.CanonicalOrder import path
DkNNRealQ.pow_le_pow and available strict power lemmas
DkReal.LeftSeparatedAt and mk strict-order bridge names
DkMath.lean and DkMath.PowerSwap import effects
```

Record any renamed API in the module docstring before adapting the plan.

### Phase 1: Stabilize the existing structural core

Add:

```text
DkMath/PowerSwap/Frame.lean
```

Define only natural-exponent generic frames:

```lean
structure NatPowerFrame (α : Type u) where
  base : α
  degree : Nat

def NatPowerFrame.eval [Pow α Nat] (A : NatPowerFrame α) : α

def NatPowerFrame.power
    (A : NatPowerFrame α) (m : Nat) : NatPowerFrame α
```

Avoid `Pow α α` initially. Real exponents already belong to `Branch`.

The data definitions require only `[Pow α Nat]`. Theorems using
`(a ^ n) ^ m = a ^ (n * m)` must be placed in a section with `[Monoid α]`, or
another explicit structure that supplies `pow_mul`. This law must not be
claimed from an arbitrary `Pow` instance.

Preserve `PowNormalForm` for compatibility. Relate it to
`NatPowerFrame Nat` by an equivalence or conversion functions instead of
replacing it immediately.

Acceptance criteria:

```text
Frame module imports no Real analysis.
Existing NormalForm API remains source-compatible.
PowerSwap and NormalForm targeted builds pass.
```

### Phase 2: Add proof-carrying normalization

Add:

```text
DkMath/PowerSwap/Normalize.lean
```

Use one frame type rather than duplicating `NormalNatPowerFrame`:

```lean
structure NormalizesTo [Pow α Nat]
    (source target : NatPowerFrame α) : Prop where
  value_eq : source.eval = target.eval
```

Provide reflexivity, symmetry, and transitivity using equality alone.
Composition with `NatPowerFrame.power` belongs in a `[Monoid α]` section
because its evaluation theorem depends on `pow_mul`.

Relate `HasPowNormalForm` to this generic witness. Do not implement arbitrary
root extraction.

### Phase 3: Add comparison specifications

Add:

```text
DkMath/PowerSwap/Compare.lean
```

Define:

```text
SameDegree
SameDegreeComparison
SameDegreeStrictComparison
```

The strict specification must carry positive degree:

```lean
structure SameDegreeStrictComparison [LT α]
    (A B : NatPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  degree_pos : 0 < A.degree
  base_lt : A.base < B.base
```

Prove generic evaluation theorems from explicit monotonicity hypotheses. Keep
the core independent of `DkNNRealQ` and avoid requiring `LinearOrder`.

This phase specifies comparison; it does not claim decidability.

### Phase 4: Add Cosmic frames

Add:

```text
DkMath/PowerSwap/CosmicFrame.lean
```

Define:

```lean
structure CosmicPowerFrame (α : Type u) where
  core : α
  gap : α
  degree : Nat

def CosmicPowerFrame.base [Add α] (A) := A.core + A.gap
def CosmicPowerFrame.eval [Add α] [Pow α Nat] (A) := A.base ^ A.degree
```

Use `core` and `gap` names to align with the implemented DkReal canonical Gap
API. Add conversion to `NatPowerFrame`.

### Phase 5: Add the DkNNRealQ bridge

Add:

```text
DkMath/Analysis/DkReal/PowerSwapBridge.lean
```

This module should import `CanonicalOrder` and the structural PowerSwap
modules, but not the analytic branch.

Initial theorems:

```text
NatPowerFrame.evalDk
CosmicPowerFrame.evalDk
eval_le_of_sameDegree_base_le
eval_lt_of_sameDegree_base_lt, with 0 < degree
eval_eq_of_normalizesTo
cosmic_eval_le
```

The non-strict theorem can use the existing `DkNNRealQ.pow_le_pow`. The strict
theorem should use Mathlib's power monotonicity supplied by the new
`IsStrictOrderedRing` instance, with an explicit nonzero-degree hypothesis.

### Phase 6: Add finite observation comparison

Add:

```text
DkMath/Analysis/DkReal/PowerSwapObservation.lean
```

Suggested API:

```lean
inductive StageComparison
  | left
  | overlap
  | right

def compareAt (x y : DkNNReal) (n : Nat) : StageComparison

structure StrictCertificate (x y : DkNNReal) where
  stage : Nat
  separated : DkReal.LeftSeparatedAt x.val y.val stage

def compareUpTo (fuel : Nat) (x y : DkNNReal) :
  Option (StrictCertificate x y ⊕ StrictCertificate y x)
```

Prove soundness only:

```text
left result  -> mk x < mk y
right result -> mk y < mk x
none         -> no conclusion beyond the searched prefix
```

Do not state completeness for finite fuel.

The use of `DkNNReal` here is deliberate: endpoint inspection is a
representative operation. Soundness must conclude statements about
`DkNNRealQ.mk x` and `DkNNRealQ.mk y`; `compareAt` must not be defined directly
on quotient values.

### Phase 7: Refine module exports

Keep `DkMath.PowerSwap` as the compatibility umbrella. Add a lightweight
entry point:

```text
DkMath.PowerSwap.Core
```

re-exporting:

```text
Basic
Exchange
NormalForm
Frame
Normalize
Compare
CosmicFrame
```

Treat `Branch` and `Contours` as the analytic layer. Moving files into an
`Analytic` directory is optional and should only be done with compatibility
re-export modules.

Add a thin analytic entry point:

```text
DkMath.PowerSwap.Analytic
  imports Branch and Contours
```

New structural consumers must import `DkMath.PowerSwap.Core`, not the umbrella.

### Phase 8: Consumer bridges

Only after the structural and DkNNRealQ bridges stabilize:

1. replace the placeholder `DkMath.FLT.PowerSwapBridge` with narrowly scoped
   theorems;
2. connect normalized frames to Sequence/KUS where a concrete consumer exists;
3. add analytic contour comparison theorems on domains where
   `harmonicCoord` is monotone.

## 7. Explicit non-goals

The next implementation cycle should not attempt:

```text
global DecidableLE DkNNRealQ
global LinearOrder DkNNRealQ
arbitrary d-th roots in DkNNRealQ
canonical factorization of every Nat into a unique power frame
automatic normalization of arbitrary unequal degrees
moving or renaming all existing analytic modules at once
```

## 8. Recommended execution order

The smallest low-risk sequence is:

```text
0. Reconfirm live names and imports
1. Frame
2. Normalize
3. Compare
4. CosmicFrame
5. PowerSwapBridge for DkNNRealQ
6. finite StageComparison on DkNNReal and quotient soundness
7. Core and Analytic public entry points
8. consumer bridges
```

Each phase should add one module, build that target immediately, then build
`DkMath.PowerSwap`, `DkMath.Analysis.DkReal`, and `DkMath`.

## 9. Final assessment

The original design direction remains valid, but its historical commit order
no longer matches the repository. The analytic branch is already advanced,
while the abstract structural and comparison middle layers are absent.

The feasible route is not to restart PowerSwap. It is to fill the missing
middle:

```text
existing Nat normal form
  -> generic natural-exponent frame
  -> normalization witness
  -> same-degree comparison specification
  -> DkNNRealQ bridge
  -> finite certified observation
```

This preserves the implemented mathematics and gives decidable comparison a
precise role: finite observations and structural data are computable, while
full asymptotic quotient comparison remains proof-theoretically total without
being installed as a global decision procedure.
