# EuclideanGeometry-260722 — Implementation Design

## 1. Purpose

This design joins two independently developed DkMath routes.

```text
Route A — CF2D phase and orbit
  normalized 1/k division
  additive kernel family
  finite kernel product
  finite action return
  exact finite orbit

Route B — Gauss–Wantzel arithmetic
  powers of two
  distinct Fermat-prime factors
  quadratic constructibility
```

The integration theorem is not that Fermat-form indices are the only indices whose CF2D orbit closes. The CF2D real trigonometric orbit closes for every positive division count.

The Gauss–Wantzel condition classifies which one-step orbit generators are obtainable through finite quadratic construction.

The central conceptual separation is therefore:

```text
periodicity exists for every positive k;
constructibility selects special k.
```

## 2. Existing architecture

### 2.1. Algebraic CF2D layer

The generic algebraic base consists of:

```text
Vec R
Vec.q2
Vec.one
Vec.star
Vec.conj
UnitKernel R
UnitKernel.one
UnitKernel.star
UnitKernel.conj
UnitKernel.act
LevelSet R rho2
```

The essential laws already exist.

$$
q_2(r\star z)=q_2(r)q_2(z)
$$

$$
q_2(r)=1\Longrightarrow q_2(r\star z)=q_2(z)
$$

The kernel multiplication is associative and commutative over a commutative ring. Conjugation supplies an inverse for unit kernels.

### 2.2. Additive kernel-family layer

`KernelFamily T R` packages a map from an additive parameter into unit kernels.

```lean
kernel : T → UnitKernel R
map_zero : kernel 0 = neutral
map_add : kernel (t + s) = kernel t star kernel s
```

Its coordinate projections are:

```text
cfcos = core coordinate
cfsin = beam coordinate
```

The real model is already supplied by:

```text
realTrigKernelFamily.kernel theta
```

with coordinates `Real.cos theta` and `Real.sin theta`.

### 2.3. Scalar cycle-division layer

The semantic phase-shift implementation already defines:

```lean
normalizedCycleStep k = 1 / k
```

and proves for positive `k`:

$$
k\cdot\operatorname{normalizedCycleStep}(k)=1.
$$

This theorem is purely scalar. It neither names a circle nor implies a unit-kernel return by itself.

### 2.4. Iteration and finite-order layer

The semantic DkReal bridge already contains:

```text
semanticActIter
semanticOrbit
SemanticPeriodic
SemanticFiniteOrder
semanticMinimalPeriod
semanticKernelPower
SemanticKernelFiniteOrder
```

This layer proves that kernel-product return and plane-action return correspond in its transported setting. It also supplies a complete exact-order-four prototype.

The new general route should be extracted at the generic `UnitKernel R` and `KernelFamily T R` layers rather than remaining tied to first-quadrant `DkNNRealQ` kernels.

### 2.5. Euclidean interpretation layer

`EuclideanPhase.lean` already interprets:

```text
q2 level set
  -> coordinate circle equation
  -> standard EuclideanSpace Real (Fin 2)
```

It also identifies the core-zero action with the oriented rotation by `Real.pi / 2`.

This is a later model of the algebraic action. The general-angle bridge should extend this architecture.

## 3. Proposed package structure

```text
DkMath/CosmicFormula/Rotation/CF2D/
  KernelPower.lean
  CycleDivision.lean
  RegularOrbit.lean
  EuclideanRegularOrbit.lean

DkMath/NumberTheory/EuclideanGeometry/
  FermatForm.lean
  QuadraticConstructible.lean
  GaussWantzelBridge.lean

DkMath/EuclideanGeometry.lean
```

### 3.1. `KernelPower.lean`

Responsibilities:

```text
standard algebra instances or a scoped equivalent
kernel natural-power API
KernelFamily.kernel_nsmul
kernel action iteration bridge
exact-order predicate and orderOf bridge
```

This module must not import `Real`, `DkReal`, topology, or Euclidean geometry.

### 3.2. `CycleDivision.lean`

Responsibilities:

```text
abstract full-cycle parameter
positive k-division return theorem
normalized phase-to-angle bridge
real regular one-step kernel
k-fold return theorem
```

The generic theorem is parameterized by a period. The real specialization chooses a standard full-cycle interpretation.

### 3.3. `RegularOrbit.lean`

Responsibilities:

```text
kernelOrbitVertex
generic q2 preservation
successor action
periodic index law
exact-order injectivity
Fin k wrapper
real regular orbit specialization
```

No Euclidean terms should appear here.

### 3.4. `EuclideanRegularOrbit.lean`

Responsibilities:

```text
general real-trigonometric action as oriented rotation
transport of regular orbit vertices
comparison with equal-angle Euclidean orbit
```

No constructibility arithmetic should appear here.

### 3.5. `FermatForm.lean`

Responsibilities:

```text
Fermat number compatibility wrapper when needed
IsGaussWantzelIndex
closure facts for powers of two
finite products of distinct Fermat primes
Euler-totient bridge
small examples
```

This module should import existing number-theory infrastructure, not CF2D.

### 3.6. `QuadraticConstructible.lean`

Responsibilities:

```text
algebraic constructibility representation
semantic evaluation
closure under arithmetic and square root
coordinatewise constructible unit kernels
constructible orbit closure under repeated kernel action
```

This module is likely larger and may remain a staged implementation beyond the first branch checkpoint.

### 3.7. `GaussWantzelBridge.lean`

Responsibilities:

```text
connect IsGaussWantzelIndex to constructible phase generator
connect constructible generator to ConstructibleUnitKernel
connect ConstructibleUnitKernel to ConstructibleRegularOrbit
state the final classification theorem only when both directions are proved
```

## 4. Core algebra design

## 4.1. Standard multiplication interface

The current explicit operation is:

```lean
UnitKernel.star r s
```

The preferred public algebra surface is:

```lean
r * s
r ^ n
r⁻¹
1
orderOf r
```

The instances should be definitional wrappers around the existing operations.

```lean
instance [CommRing R] : One (UnitKernel R) :=
  ⟨UnitKernel.one R⟩

instance [CommRing R] : Mul (UnitKernel R) :=
  ⟨UnitKernel.star⟩

instance [CommRing R] : Inv (UnitKernel R) :=
  ⟨UnitKernel.conj⟩
```

Then package a `CommGroup` using existing theorems.

Compatibility concern: existing simplification lemmas use explicit names such as `star_one`. Add bridge simplification lemmas carefully so `simp` does not loop between `Mul.mul` and `UnitKernel.star` spellings.

Recommended direction:

```text
explicit definitions remain canonical internally;
standard notation is a public interface;
new simp lemmas reduce notation to existing operations.
```

## 4.2. Natural-power theorem

The central algebra theorem is:

$$
K(n\cdot t)=K(t)^n.
$$

Lean surface:

```lean
theorem KernelFamily.kernel_nsmul
    (F : KernelFamily T R) (n : ℕ) (t : T) :
    F.kernel (n • t) = (F.kernel t) ^ n
```

Proof skeleton:

```text
n = 0:
  kernel 0 = 1

n + 1:
  (n + 1) • t = n • t + t
  kernel addition becomes kernel multiplication
  induction hypothesis
  power successor
```

The multiplication order is harmless because the unit-kernel group is commutative, but the proof should align with Lean's selected `pow_succ` orientation rather than relying on commutativity unnecessarily.

## 4.3. Action iteration theorem

For a fixed kernel `r`, define or reuse:

```lean
def kernelActIter (r : UnitKernel R) (n : ℕ) (z : Vec R) : Vec R :=
  (UnitKernel.act r)^[n] z
```

Prove:

$$
\operatorname{act}(r^n,z)=\operatorname{actIter}(r,n,z).
$$

This is the generic counterpart of the existing semantic theorem.

Candidate theorem:

```lean
theorem UnitKernel.pow_act
    (r : UnitKernel R) (n : ℕ) (z : Vec R) :
    UnitKernel.act (r ^ n) z = (UnitKernel.act r)^[n] z
```

This theorem turns a kernel return directly into action return.

## 5. Cycle-division design

## 5.1. Abstract period theorem

Let `F : KernelFamily T R`. A period is a parameter `period : T` satisfying:

$$
F(period)=1.
$$

A `k`-division step is a parameter `step : T` satisfying:

$$
k\cdot step=period.
$$

Then:

$$
F(step)^k=1.
$$

Lean surface:

```lean
theorem KernelFamily.kernel_pow_eq_one_of_nsmul_eq_period
    (F : KernelFamily T R)
    {k : ℕ} {step period : T}
    (hstep : k • step = period)
    (hperiod : F.kernel period = 1) :
    (F.kernel step) ^ k = 1
```

The positivity hypothesis is not algebraically required once `hstep` is supplied. Positivity belongs to the normalized scalar specialization because `1 / k` requires nonzero `k`.

Action corollary:

```lean
theorem KernelFamily.act_iterate_eq_of_nsmul_eq_period
    ... :
    (UnitKernel.act (F.kernel step))^[k] = id
```

## 5.2. Normalized phase convention

Select a normalized phase coordinate:

$$
p\in\mathbb R,
$$

where one full cycle is represented by `p = 1`.

The Euclidean angle interpretation is:

$$
\Theta(p)=2\pi p.
$$

Definitions:

```lean
def normalizedPhaseAngle (p : ℝ) : ℝ :=
  p * (2 * Real.pi)

noncomputable def normalizedPhaseKernel (p : ℝ) : UnitKernel ℝ :=
  realTrigKernelFamily.kernel (normalizedPhaseAngle p)
```

The family `normalizedPhaseKernel` should be packaged as a `KernelFamily ℝ ℝ` if this avoids repeating angle-addition proofs.

Candidate:

```lean
noncomputable def normalizedRealKernelFamily : KernelFamily ℝ ℝ where
  kernel p := realTrigKernelFamily.kernel (normalizedPhaseAngle p)
  map_zero := ...
  map_add := ...
```

Then define:

```lean
noncomputable def regularKernel (k : ℕ) : UnitKernel ℝ :=
  normalizedRealKernelFamily.kernel (normalizedCycleStep k)
```

For positive `k`, the scalar theorem yields:

$$
k\cdot\frac1k=1.
$$

The full-cycle kernel theorem needs:

$$
K(1)=1.
$$

This follows from the standard real trigonometric period:

$$
\cos(2\pi)=1,
\qquad
\sin(2\pi)=0.
$$

The desired proof chain is therefore explicit:

```text
normalizedCycleStep_mul_returnCount
  -> nsmul equality in Real
  -> KernelFamily.kernel_nsmul
  -> normalized full-cycle kernel is neutral
  -> regularKernel_pow_eq_one
```

## 5.3. Zero-division behavior

`normalizedCycleStep 0` is currently a real division expression and evaluates according to field conventions. It must not be interpreted as a valid cycle division.

All semantic regular-kernel theorems should require:

```lean
0 < k
```

or a stronger lower bound.

Avoid a dependent subtype in the first implementation unless it significantly reduces repeated hypotheses.

## 6. Exact-order design

## 6.1. Predicate

```lean
def ExactKernelOrder (r : UnitKernel R) (k : ℕ) : Prop :=
  r ^ k = 1 ∧
    ∀ m : ℕ, 0 < m → m < k → r ^ m ≠ 1
```

This follows the already successful order-four style, generalized to arbitrary `k`.

## 6.2. `orderOf` bridge

When `k > 0`, prove:

```lean
ExactKernelOrder r k ↔ orderOf r = k
```

The exact Mathlib theorem surface should be investigated first. It may be more stable to prove two directional lemmas rather than one large `iff`.

## 6.3. Minimality of the regular kernel

The one-step Euclidean angle is:

$$
\theta_k=\frac{2\pi}{k}.
$$

The `m`th power has coordinates:

$$
\left(\cos\frac{2\pi m}{k},\sin\frac{2\pi m}{k}\right).
$$

For `0 < m < k`, the angle lies strictly between `0` and `2π`, so the pair cannot equal `(1,0)`.

Possible proof routes:

### Route 1 — trigonometric zero classification

Use existing theorems characterizing simultaneous values:

```text
cos x = 1
sin x = 0
```

as integer multiples of `2π`.

Advantages:

```text
small conceptual distance from current real kernel
no additional complex algebra bridge
```

Risk:

```text
exact theorem names and normalization may be awkward
```

### Route 2 — complex exponential

Map `UnitKernel ℝ` to the unit complex number:

$$
(a,b)\mapsto a+bi.
$$

Then `regularKernel k` maps to:

$$
\exp\left(2\pi i/k\right).
$$

Use primitive-root or exponential equality theorems.

Advantages:

```text
finite-order structure is natural
likely reusable by constructibility/cyclotomic work
```

Risk:

```text
requires a new multiplicative equivalence and careful theorem discovery
```

### Route 3 — oriented-angle quotient

Use Mathlib's angle quotient and prove the `m`th angle class is nonzero.

Advantages:

```text
matches Euclidean interpretation
```

Risk:

```text
quotient API may be more elaborate than needed
```

The implementation should prototype all three with small `example` declarations, then select the shortest stable route.

## 7. Orbit design

## 7.1. Generic orbit

```lean
def kernelOrbitVertex
    (r : UnitKernel R) (z : Vec R) (j : ℕ) : Vec R :=
  UnitKernel.act (r ^ j) z
```

Laws:

$$
q_2(v_j)=q_2(z).
$$

$$
v_{j+1}=r\star v_j.
$$

If `r^k = 1`, then:

$$
v_{j+k}=v_j.
$$

## 7.2. Faithful base point

Choose:

```lean
Vec.one R = (1,0)
```

Then:

$$
\operatorname{act}(r,\operatorname{one})=r.
$$

Thus equality of orbit vertices at the neutral base is equality of kernel powers. This makes exact-order injectivity elementary.

Required lemma:

```lean
@[simp] theorem UnitKernel.act_vecOne (r : UnitKernel R) :
  UnitKernel.act r (Vec.one R) = (r : Vec R)
```

## 7.3. Finite orbit wrapper

```lean
def FiniteKernelOrbit (r : UnitKernel R) (k : ℕ) :=
  Fin k → Vec R
```

Specialization:

```lean
noncomputable def regularVertex (k : ℕ) (j : Fin k) : Vec ℝ :=
  kernelOrbitVertex (regularKernel k) (Vec.one ℝ) j.val
```

Theorems:

```text
regularVertex_q2
regularVertex_succ_mod
regularVertex_injective
regularVertex_card_range
```

The cardinality theorem is a useful algebraic replacement for saying “there are k polygon vertices.”

## 8. Euclidean design

## 8.1. General rotation bridge

The current Euclidean implementation proves the quarter-turn by transporting to complex coordinates. The same complex-coordinate isometry should support arbitrary real angle.

The desired commuting diagram is:

```text
Vec Real
  -- CF2D act by (cos theta, sin theta) --> Vec Real
      |                                         |
      v                                         v
EuclideanPlane
  -- oriented rotation theta ----------------> EuclideanPlane
```

A proof through complex coordinates should reduce both paths to multiplication by:

$$
\cos\theta+i\sin\theta.
$$

Prefer a theorem comparing both sides after `euclideanPlaneComplexIsometry`, then use injectivity.

## 8.2. Euclidean regular orbit

Define only a transported vertex function.

```lean
noncomputable def euclideanRegularVertex (k : ℕ) (j : Fin k) : EuclideanPlane :=
  pairToEuclideanPlane (Vec.toProd (regularVertex k j))
```

Prove:

```text
all vertices lie on the unit metric sphere
each successor is rotation by 2π/k
vertices are distinct when exact order is known
```

Do not introduce edge segments or convexity in v0.

## 9. Fermat-form arithmetic design

## 9.1. Classical target

For `n ≥ 3`, classical constructibility is characterized by:

$$
n=2^a\prod_{i\in S}F_i,
$$

where each selected Fermat number is prime and no index is repeated.

A Fermat number is:

$$
F_i=2^{2^i}+1.
$$

Use a repository-local wrapper only if Mathlib lacks an appropriately named definition.

## 9.2. Predicate

```lean
def IsGaussWantzelIndex (n : ℕ) : Prop :=
  ∃ a : ℕ, ∃ s : Finset ℕ,
    (∀ i ∈ s, Nat.Prime (fermatNumber i)) ∧
    n = 2 ^ a * ∏ i ∈ s, fermatNumber i
```

Potential strengthening:

```text
exclude zero index when theorem requires n ≥ 3;
include a squarefree odd-part characterization;
include an Euler-totient power-of-two characterization.
```

The base predicate should remain close to the theorem statement.

## 9.3. Totient bridge

For a factorization:

$$
n=2^a\prod q_i^{e_i},
$$

`φ(n)` is a power of two exactly when:

```text
every odd exponent e_i equals one;
every q_i minus one is a power of two;
every such prime q_i is a Fermat prime.
```

This arithmetic theorem can be formalized independently of constructible fields.

GN5 should not replace Euler-totient theory. A GN divisibility theorem may be used as a local lemma only if its exact statement matches one of the required factor arguments.

## 10. Constructibility design

## 10.1. Algebraic first representation

A direct geometric construction API introduces line and circle degeneracies, unordered intersection pairs, and incidence obligations. The first DkMath implementation should therefore encode quadratic construction algebraically.

One possible syntax:

```lean
inductive QuadraticExpr
  | rat : ℚ → QuadraticExpr
  | add : QuadraticExpr → QuadraticExpr → QuadraticExpr
  | neg : QuadraticExpr → QuadraticExpr
  | mul : QuadraticExpr → QuadraticExpr → QuadraticExpr
  | inv : QuadraticExpr → proof_nonzero → QuadraticExpr
  | sqrt : QuadraticExpr → proof_nonnegative → QuadraticExpr
```

Dependent proof arguments inside an inductive can make recursion cumbersome. A cleaner alternative is an unverified expression syntax plus a semantic predicate recording that each inverse and square root is valid.

A field-tower representation may align better with standard algebra, but likely costs more infrastructure. Prototype both before committing.

## 10.2. Semantic evaluation

```lean
noncomputable def QuadraticExpr.eval : QuadraticExpr → ℝ
```

Then define:

```lean
def QuadraticallyConstructible (x : ℝ) : Prop :=
  ∃ e : QuadraticExpr, e.Valid ∧ e.eval = x
```

Prove closure under:

```text
0, 1, rational constants
addition and subtraction
multiplication
inverse
nonnegative square root
```

## 10.3. Kernel and orbit constructibility

```lean
def ConstructibleUnitKernel (r : UnitKernel ℝ) : Prop :=
  QuadraticallyConstructible (r : Vec ℝ).core ∧
  QuadraticallyConstructible (r : Vec ℝ).beam
```

Kernel product preserves constructibility because its coordinates use ring operations.

Therefore:

```lean
theorem constructible_kernel_power ...
```

and:

```lean
theorem constructible_regular_orbit_of_constructible_kernel ...
```

are lower-cost than proving the Gauss–Wantzel classification itself.

## 10.4. Final bridge target

The eventual theorem should be stated only after the constructibility semantics are mathematically equivalent to the intended straightedge-and-compass notion.

Target:

```lean
theorem constructibleRegularOrbit_iff_gaussWantzel
    (n : ℕ) (hn : 3 ≤ n) :
    ConstructibleRegularOrbit n ↔ IsGaussWantzelIndex n
```

Before the geometric/algebraic equivalence is proved, use an explicit name such as:

```text
QuadraticallyConstructibleRegularOrbit
```

rather than the unqualified word `Constructible`.

## 11. Dependency order

```text
Basic
  -> KernelPower
  -> CycleDivision
  -> RegularOrbit
  -> EuclideanRegularOrbit

Number theory base
  -> FermatForm
  -> QuadraticConstructible
  -> GaussWantzelBridge

RegularOrbit + GaussWantzelBridge
  -> DkMath.EuclideanGeometry
```

No import from the number-theory constructibility package should flow back into generic CF2D.

## 12. Theorem checkpoints

### Checkpoint A — algebraic repetition

```text
UnitKernel standard algebra interface
KernelFamily.kernel_nsmul
UnitKernel.pow_act
```

### Checkpoint B — normalized return

```text
normalizedRealKernelFamily
regularKernel
regularKernel_pow_eq_one
regularKernel action return
```

### Checkpoint C — finite orbit

```text
kernelOrbitVertex
q2 preservation
period law
Fin wrapper
```

### Checkpoint D — exact order

```text
ExactKernelOrder
orderOf bridge
regularKernel_exactOrder
regularVertex_injective
```

### Checkpoint E — Euclidean bridge

```text
general-angle action comparison
unit-sphere membership
equal-angle successor theorem
```

### Checkpoint F — arithmetic target

```text
IsGaussWantzelIndex
small positive and negative examples
totient power-of-two bridge
```

### Checkpoint G — constructibility

```text
quadratic expression or tower representation
constructible unit kernel
constructible orbit
Gauss and Wantzel directions
```

## 13. Small examples

Use examples as API tests, not as substitutes for general proofs.

Expected constructible indices:

```text
3
4
5
8
15
17
```

Expected non-constructible indices:

```text
7
9
25
```

The regular CF2D kernel return theorem should still hold for `7`, `9`, and `25`. Their negative status belongs only to the quadratic constructibility predicate.

This contrast should be represented in tests because it captures the purpose of the integration.

## 14. Correctness boundaries

The following implications are valid targets.

```text
normalized scalar division
  + additive kernel family
  + full-cycle period
  -> kernel return

kernel return
  -> action return

exact kernel order
  -> distinct Fin k orbit at a faithful base

constructible one-step kernel
  -> constructible finite orbit

Gauss–Wantzel arithmetic condition
  <-> quadratic constructibility of the regular generator
```

The following implications are invalid without extra hypotheses.

```text
scalar return
  -/-> kernel return

kernel return
  -/-> exact order

closed orbit
  -/-> distinct orbit

distinct cyclic orbit
  -/-> straightedge-and-compass constructibility

q2 preservation
  -/-> Euclidean circle assumption before interpretation
```

## 15. v0 deliverable

The branch should prioritize a complete, reusable algebraic chain over a premature full historical theorem.

The preferred v0 completion is:

```text
KernelFamily.kernel_nsmul
normalized phase family
regularKernel_pow_eq_one
generic regular orbit
q2 and period laws
exact order when feasible
general Euclidean rotation bridge
IsGaussWantzelIndex definition and arithmetic scaffolding
constructibility design with at least closure lemmas
```

The full Gauss–Wantzel equivalence may require a later branch if the quadratic-field tower infrastructure is larger than the CF2D integration itself.
