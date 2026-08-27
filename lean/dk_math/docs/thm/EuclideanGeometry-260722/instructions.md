# EuclideanGeometry-260722 — Implementation Instructions

## Mission

Connect the already-implemented CF2D normalized-cycle division law to the already-implemented unit-kernel family, finite iteration, orbit, and Euclidean interpretation layers.

The immediate theorem program is not to draw a polygon first. It is to prove the following pre-geometric chain.

```text
positive division count k
  -> normalized scalar step 1 / k
  -> one-step unit kernel
  -> k-fold kernel product
  -> return to the neutral kernel
  -> k-fold action return on every q2 boundary
  -> exact order when no smaller positive iterate returns
  -> finite orbit of distinct boundary points
  -> later Euclidean reading as a regular polygon
```

The Gauss–Wantzel layer is then attached as a separate classification of which one-step kernels are constructible by a finite tower of quadratic constructions.

Do not make circular geometry, angle measure, or a regular polygon definition an input to the CF2D return theorem.

## Repository and branch

Repository:

```text
Deskuma/dkmath
```

Work branch:

```text
thm/EuclideanGeometry-260722-v0
```

The branch has already been created from:

```text
develop
```

Documentation directory:

```text
lean/dk_math/docs/thm/EuclideanGeometry-260722/
```

Do not merge, rebase, open a pull request, or modify another branch.

## Source of truth

Inspect the current branch before editing. At minimum read:

```text
DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
DkMath/CosmicFormula/Rotation/CF2D/Trig.lean
DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean
DkMath/CosmicFormula/Rotation/CF2D/Real.lean
DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
DkMath/Analysis/DkReal/SemanticCF2D.lean
DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean
DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
```

Confirm exact namespaces, imports, theorem names, argument order, and current typeclass assumptions. Do not copy theorem signatures from this document without checking the code.

The current toolchain is Lean 4.29.0. Do not assume declarations from a newer Mathlib version exist.

## Existing implementation facts to preserve

The current repository already contains these facts.

```text
Vec.q2
  two-component square mass

Vec.star
  algebraic kernel product

Vec.q2_star
  multiplicativity of q2 under star

UnitKernel.one
UnitKernel.star
UnitKernel.conj
UnitKernel.star_assoc
UnitKernel.star_comm
UnitKernel.star_conj
UnitKernel.conj_star

KernelFamily.kernel_zero_one
KernelFamily.kernel_add_star
KernelFamily.cfcos
KernelFamily.cfsin

realTrigKernelFamily
  kernel t has coordinates Real.cos t and Real.sin t

normalizedCycleStep k
  scalar value 1 / k

normalizedCycleStep_mul_returnCount
  k * normalizedCycleStep k = 1 for positive k

semanticActIter
semanticOrbit
SemanticPeriodic
SemanticFiniteOrder
semanticMinimalPeriod
semanticKernelPower
SemanticKernelFiniteOrder
semanticKernelFiniteOrder_iff

SemanticExactKernelOrderFour
SemanticExactActionOrderFour

EuclideanPhase
  q2 level-set interpretation and the order-four quarter-turn bridge
```

The new implementation must reuse these layers. Do not create a parallel replacement API unless a concrete blocker is first demonstrated.

## Critical mathematical separation

Keep three statements separate.

```text
Scalar return:
  k * (1 / k) = 1

Kernel return:
  the k-fold product of the one-step kernel is neutral

Exact order:
  the k-fold product is neutral and no smaller positive product is neutral
```

The scalar identity alone does not prove kernel return. Kernel return needs the additive-homomorphism law of `KernelFamily` and a declared full-cycle period.

Kernel return alone does not prove exact order. Exact order needs a separate minimality argument.

Constructibility is a fourth, independent layer.

```text
Constructibility:
  the one-step kernel coordinates are obtainable by finitely many quadratic construction steps
```

Do not identify constructibility with periodicity.

## File plan

Prefer small modules with one obligation each. Adjust names only when repository conventions require it.

```text
DkMath/CosmicFormula/Rotation/CF2D/KernelPower.lean
DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean
DkMath/CosmicFormula/Rotation/CF2D/RegularOrbit.lean
DkMath/CosmicFormula/Rotation/CF2D/EuclideanRegularOrbit.lean
DkMath/NumberTheory/EuclideanGeometry/FermatForm.lean
DkMath/NumberTheory/EuclideanGeometry/GaussWantzelBridge.lean
DkMath/EuclideanGeometry.lean
```

Do not place the algebraic `KernelFamily` natural-number iteration theorem under `DkReal`. It belongs to the generic CF2D algebraic layer.

Do not place the Fermat-form predicate inside CF2D. It belongs to number theory or a dedicated `EuclideanGeometry` namespace.

## Phase EUC-001 — Standard unit-kernel algebra interface

First inspect whether adding standard instances to `UnitKernel R` causes conflicts.

Desired interface over `[CommRing R]`:

```lean
instance : One (UnitKernel R)
instance : Mul (UnitKernel R)
instance : Inv (UnitKernel R)
instance : CommGroup (UnitKernel R)
```

Use the existing definitions:

```text
One.one  := UnitKernel.one R
Mul.mul  := UnitKernel.star
Inv.inv  := UnitKernel.conj
```

Reuse existing identity, associativity, commutativity, and inverse theorems.

If global instances create elaboration regressions, do not force them into `Basic.lean`. Instead create an isolated module with local or scoped instances and record the obstruction. The implementation must remain compatible with existing explicit `UnitKernel.star` users.

Required checks:

```lean
#check (1 : UnitKernel ℝ)
#check fun r : UnitKernel ℝ => r ^ 5
#check fun r : UnitKernel ℝ => orderOf r
```

## Phase EUC-002 — Natural-number multiplication bridge

Prove a generic theorem connecting additive parameter repetition to kernel multiplication.

Preferred standard-power surface, when Phase EUC-001 succeeds:

```lean
theorem KernelFamily.kernel_nsmul
    (F : KernelFamily T R) (n : ℕ) (t : T) :
    F.kernel (n • t) = (F.kernel t) ^ n
```

Expected assumptions:

```text
[AddMonoid T]
[CommRing R]
```

Prove by induction on `n`, using `kernel_zero_one`, `kernel_add_star`, and the chosen power recursion theorem.

Also expose action and coordinate consequences only when they shorten downstream proofs.

Candidate consequences:

```lean
theorem KernelFamily.act_nsmul ...
theorem KernelFamily.cfcos_nsmul ...
theorem KernelFamily.cfsin_nsmul ...
```

Do not expand coordinates unless necessary. The kernel equality is primary.

Fallback surface, if standard `Pow` is not adopted:

```lean
def KernelFamily.kernelPower (F : KernelFamily T R) (t : T) : ℕ → UnitKernel R

theorem KernelFamily.kernel_nsmul_eq_kernelPower ...
```

Record which surface was selected and why.

## Phase EUC-003 — Abstract full-cycle division

Introduce a theorem that does not mention `Real.pi`.

The theorem should accept:

```text
F       additive unit-kernel family
period  a parameter whose kernel is neutral
step    a parameter repeated k times to reach period
k > 0
```

Candidate theorem:

```lean
theorem KernelFamily.kernel_pow_eq_one_of_nsmul_eq_period
    (F : KernelFamily T R)
    {k : ℕ} (hk : 0 < k)
    {step period : T}
    (hstep : k • step = period)
    (hperiod : F.kernel period = 1) :
    (F.kernel step) ^ k = 1
```

A variant using `F.kernel period = F.kernel 0` is acceptable when it composes better with existing APIs.

Then derive action return:

```lean
theorem KernelFamily.iterate_act_eq_id_of_nsmul_eq_period ...
```

The theorem must state return on all `Vec R`, not only one chosen point.

Also provide a level-set version when it is a direct corollary.

## Phase EUC-004 — Connect normalized `1 / k` to the real kernel family

Define a normalized full-cycle parameter only at the bridge layer.

Two equivalent parameter conventions are acceptable, but select exactly one and document it.

```text
Convention A:
  normalized phase p in Real
  real angle = p * (2 * Real.pi)

Convention B:
  angle parameter directly in Real
  one-step angle = 2 * Real.pi / k
```

Convention A better exposes the existing `normalizedCycleStep k = 1 / k` theorem.

Candidate definitions:

```lean
def normalizedPhaseAngle (p : ℝ) : ℝ := p * (2 * Real.pi)

def regularPhaseStep (k : ℕ) : ℝ := normalizedCycleStep k

noncomputable def regularKernel (k : ℕ) : UnitKernel ℝ :=
  realTrigKernelFamily.kernel (normalizedPhaseAngle (regularPhaseStep k))
```

Required theorem:

```lean
theorem regularKernel_pow_eq_one
    {k : ℕ} (hk : 0 < k) :
    regularKernel k ^ k = 1
```

The proof must visibly pass through both facts:

```text
k * normalizedCycleStep k = 1
KernelFamily.kernel_nsmul
```

Do not prove the theorem solely by an opaque trigonometric tactic if that hides the intended connection.

## Phase EUC-005 — Exact order

Define a general exact-order predicate before specializing to the real trigonometric kernel.

Candidate structure:

```lean
def ExactKernelOrder (r : UnitKernel R) (k : ℕ) : Prop :=
  r ^ k = 1 ∧
    ∀ m : ℕ, 0 < m → m < k → r ^ m ≠ 1
```

When standard group order is available, prove a bridge to `orderOf` for positive `k`.

```lean
theorem exactKernelOrder_iff_orderOf_eq ...
```

Then prove exact order for `regularKernel k` under a suitable lower bound, preferably `2 ≤ k` or `3 ≤ k` depending on the theorem used.

The minimality proof is a distinct checkpoint. Investigate in this order:

```text
1. Existing Mathlib theorems for Real.sin and Real.cos zeros.
2. Existing complex exponential primitive-root theorems.
3. Existing `Real.Angle` quotient API.
4. A direct inequality proof for 0 < m < k.
```

Choose the route with the smallest stable dependency surface under Lean 4.29.0.

Do not leave exact order as an unproved assumption in a theorem named as a completed regular-orbit theorem. If the generic return theorem is completed but minimality is blocked, publish the return theorem and mark exact-order work as an explicit TODO checkpoint.

## Phase EUC-006 — Regular orbit without polygon geometry

Define the orbit from one kernel and one base state.

Prefer a generic definition:

```lean
def kernelOrbitVertex (r : UnitKernel R) (z : Vec R) (j : ℕ) : Vec R :=
  UnitKernel.act (r ^ j) z
```

Then specialize to the neutral base vector and the regular kernel.

Required generic theorems:

```text
orbit vertex preserves q2
successor vertex is one more kernel action
period k gives vertex (j + k) = vertex j
exact order gives injectivity on Fin k for a faithful base point
```

For the neutral base vector, use the fact that acting on `Vec.one R` recovers the kernel vector. Prove that fact explicitly if it is not already available.

Candidate public definition:

```lean
noncomputable def regularVertex (k : ℕ) (j : Fin k) : Vec ℝ :=
  kernelOrbitVertex (regularKernel k) (Vec.one ℝ) j.val
```

Required public theorems:

```lean
theorem regularVertex_q2 ...
theorem regularVertex_succ ...
theorem regularVertex_period ...
theorem regularVertex_injective ...
```

The injectivity theorem depends on exact order and should not be fabricated from `Fin` index arithmetic alone.

## Phase EUC-007 — Euclidean interpretation

Only after the algebraic orbit is complete, transport it through the existing Euclidean-plane bridge.

Do not redefine the Euclidean plane or q2 circle.

Desired theorem family:

```text
CF2D action by the real trigonometric kernel
  =
Mathlib oriented rotation by the same real angle
```

The existing order-four theorem is the test case. Generalize without weakening or replacing it.

Candidate theorem:

```lean
theorem realTrigKernel_act_euclidean_eq_rotation
    (theta : ℝ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (UnitKernel.act
      (realTrigKernelFamily.kernel theta) z)) =
    euclideanPlaneOrientation.rotation theta
      (pairToEuclideanPlane (Vec.toProd z))
```

When exact theorem names or orientations differ, adapt to the actual Mathlib API.

Then show that the transported finite orbit is the ordinary equal-angle orbit. Avoid introducing convex hulls, edges, or polygon interiors in this branch unless they are required by a downstream theorem.

## Phase EUC-008 — Fermat form predicate

Implement the number-theoretic target independently from geometric construction.

Use a predicate representing the classical integer form:

```text
n = 2^a multiplied by a finite product of pairwise distinct Fermat primes
```

Do not claim that only the five familiar Fermat primes exist.

Investigate existing Mathlib names for:

```text
Euler phi
Fermat numbers
Nat.Prime
pairwise coprimality
Finset products
squarefree
```

Prefer reusing existing definitions over creating duplicate arithmetic.

Candidate public predicate:

```lean
def IsGaussWantzelIndex (n : ℕ) : Prop :=
  ∃ a : ℕ, ∃ s : Finset ℕ,
    (∀ i ∈ s, Nat.Prime (fermatNumber i)) ∧
    n = 2 ^ a * ∏ i ∈ s, fermatNumber i
```

The finite set already enforces distinct indices. Still prove or import that distinct Fermat numbers are distinct and pairwise coprime when needed.

Also expose the equivalent totient criterion as a bridge theorem when feasible:

```lean
Nat.totient n = 2 ^ e
```

Do not route the proof through GN5 merely because the project contains GN5. Use GN divisibility results only when they genuinely discharge a stated arithmetic obligation more cleanly than Mathlib.

## Phase EUC-009 — Constructibility boundary

This branch must not pretend that Mathlib already contains a complete straightedge-and-compass Gauss–Wantzel theorem.

First inspect the pinned Mathlib for reusable algebraic components. Record exact findings.

The preferred v0 result is a precise theorem surface and dependency decomposition, not an unsound one-line theorem.

Separate these predicates:

```text
QuadraticallyConstructibleScalar
ConstructibleUnitKernel
ConstructibleRegularOrbit
IsGaussWantzelIndex
```

The recommended first representation is algebraic, based on a finite tower or expression tree generated by:

```text
rational constants
addition
subtraction
multiplication
inverse of a nonzero value
square root of a nonnegative value
```

Do not begin with line-circle intersection geometry unless a complete existing Mathlib API makes that route substantially easier.

For v0, acceptable completion levels are:

```text
Level A:
  define the predicates and prove closure lemmas

Level B:
  prove constructible kernel implies constructible orbit

Level C:
  prove the sufficient Gauss direction for selected Fermat indices

Level D:
  prove full Gauss–Wantzel equivalence
```

Do not label Level A, B, or C as the full Gauss–Wantzel theorem.

## Phase EUC-010 — Public aggregation and checks

Create:

```text
DkMath/EuclideanGeometry.lean
```

It should import only the stable public modules completed in this branch.

Add focused compile checks under the existing test convention. At minimum check:

```lean
#check KernelFamily.kernel_nsmul
#check regularKernel_pow_eq_one
#check ExactKernelOrder
#check regularVertex
#check regularVertex_q2
```

When exact order is complete, also check:

```lean
#check regularKernel_exactOrder
#check regularVertex_injective
```

Run focused builds after every phase, then the repository’s accepted broader build command.

Record:

```text
commands run
files changed
new theorem names
warnings
axioms if audited
known TODOs
```

## Required implementation reports

Create sequential reports in the documentation directory.

```text
EUC-001_REPORT.md
EUC-002_REPORT.md
...
```

Each report must contain:

```text
Goal
Repository facts inspected
Implementation
Proof route
Build command and result
New public declarations
Blocked alternatives
Next checkpoint
```

Commit each independently useful checkpoint. Do not accumulate the full project into one opaque commit.

## Success criteria

The minimum successful v0 branch proves all of the following.

```text
1. Natural additive repetition of a KernelFamily parameter equals kernel power.
2. A positive normalized 1/k phase step maps to a kernel returning after k products.
3. The corresponding action returns after k iterations on every q2 level.
4. The generated finite orbit remains on the original q2 boundary.
5. The algebraic orbit is transported to the existing Euclidean model.
6. The Fermat-form constructibility target is defined without false claims.
```

The strong success target additionally proves:

```text
7. The regular real-trigonometric kernel has exact order k.
8. The Fin k orbit is injective.
9. A rigorous constructibility predicate connects a Gauss–Wantzel index to the one-step kernel.
```

## Failure and fallback policy

Do not stop at the first unavailable Mathlib theorem.

When a route fails:

```text
1. Record the exact missing declaration or elaboration error.
2. Search the pinned Mathlib for an equivalent theorem.
3. Reduce the theorem to a smaller local lemma.
4. Preserve every completed lower layer.
5. Mark the remaining obligation precisely.
```

The branch is still valuable if it completes the generic CF2D cycle-division and regular-orbit layers while leaving the full constructibility equivalence as a documented future theorem.

## Guardrails

Do not claim:

```text
that scalar return alone proves geometric rotation;
that return count alone proves minimal period;
that every closed orbit is a regular polygon;
that Mathlib already proves Gauss–Wantzel;
that the five familiar Fermat primes are all Fermat primes;
that DkReal currently represents every signed constructible coordinate;
that a q2 boundary was assumed to be a Euclidean circle before the bridge theorem.
```

Preserve the pre-geometric ordering throughout the code and documentation.
