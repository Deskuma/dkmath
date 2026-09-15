# CPG-V1-000 — repository-first audit and planning baseline

Date: 2026-09-12  
Branch: `wip/cf2d-prime-gauge-projection-260911-v1`  
HEAD: `782660577` (`wip: docs: cf2d-prime-gauge-projection-260911-v1`)  
Base reference: `develop` / `origin/develop`

## 1. Request/document boundary

The user's request was to inspect the current workspace before implementation,
prepare the implementation plan, and prepare roadmap/report management under
this directory.

The attached
`docs/not_implements/260911-CF2D-PrimeGauge-CosmicProjection-Continuum-ImplementationPlan.md`
was treated as bounded design guidance. Its proposed theorem names, module
names, and research order are candidates to audit, not declarations that have
already been implemented or commands to claim their conclusions.

The following document constraints were adopted:

- start with the repository-first audit (`CPG-V1-000`);
- prioritize Goldbach center/seat/refinement dynamics over static normalization;
- stop at `CPG-V1-007` for an explicit information-gain verdict;
- defer Projection, mesh, and continuum work until that gate;
- keep raw/proper endpoint exceptions and candidate/primality semantics
  separate;
- do not claim Strong Goldbach, universal escape, prime existence, Twin Prime,
  Legendre, RH, or continuum prime realization.

No Lean production source was changed in this audit. The new artifacts are this
report and `ROADMAP.md`.

## 2. Workspace snapshot

The repository root is `/home/deskuma/develop/lean/dkmath`; the Lake project and
source/build working directory is `lean/dk_math`.

At the start of the audit:

- the worktree was clean;
- the current branch was `wip/cf2d-prime-gauge-projection-260911-v1`;
- the branch contained the attached-plan update and the target-directory
  `README.md`, but no numbered report or ROADMAP;
- no production paths matching `PrimeGauge`, `GoldbachPhase`,
  `GoldbachRefinement`, `ContinuumGrid`, or
  `DkMath/CosmicFormula/Projection` were present;
- the existing sample path was `DkMath/Samples/Projection.lean`.

The focused replay after the source audit completed successfully:

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.CycleDivision \
  DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit \
  DkMath.NumberTheory.Primitive.PeriodicPrimeWorld \
  DkMath.NumberTheory.Primitive.PrimeWorldRefinement \
  DkMath.NumberTheory.Primitive.PrimeWorldResidues \
  DkMath.NumberTheory.Goldbach \
  DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra \
  DkMath.Samples.Projection
```

Result: exit 0, `Build completed successfully (8721 jobs)`. The shell profile
printed an environment permission warning before Lake; Lean reported no build
error. No implementation was inferred from this replay: it validates current
compatibility only.

## 3. Existing production providers

### 3.1 CF2D exact finite orbit

`DkMath.CosmicFormula.Rotation.CF2D.CycleDivision` already defines
`regularPhaseStep` and `regularKernel` and proves:

```lean
regularPhaseStep_nsmul_eq_one
regularKernel_pow_eq_one
regularKernel_exactOrder
orderOf_regularKernel
```

The relevant source is
[CycleDivision.lean](../../../DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean:128),
with the exact-order declarations at lines 211–220. The finite orbit layer
also provides `regularVertex_next`, injectivity, and the exact range size in
[RegularOrbit.lean](../../../DkMath/CosmicFormula/Rotation/CF2D/RegularOrbit.lean:103).

Therefore `regularKernel_pow_eq_one_iff_dvd` and a phase-equality theorem are
new API bridges over an existing provider, not new exact-order mathematics.
The current Mathlib source provides `orderOf_dvd_iff_pow_eq_one`,
`pow_eq_one_iff_modEq`, and `pow_eq_pow_iff_modEq`; the latter is also exposed
as `IsOfFinOrder.pow_eq_pow_iff_modEq`. CPG-V1-001 should compose these with
`orderOf_regularKernel`, rather than re-prove the order argument.

### 3.2 Goldbach fixed-center and obstruction layers

Production `Goldbach.Basic` defines `GoldbachPairAt`, the fixed-center GN
fiber, and the admissible finite offset range. `Goldbach.Obstruction` defines
raw `GoldbachLeftObstructed` / `GoldbachRightObstructed` and the separate
`GoldbachProperObstructed`, including the proper endpoint exception.

The finite complete-cutoff equivalence and survivor semantics are owned by
[Obstruction.lean](../../../DkMath/NumberTheory/Goldbach/Obstruction.lean:22).
This means a gauge bridge must not replace proper obstruction with raw phase
avoidance without explicit endpoint hypotheses.

### 3.3 Existing paired residue observer

`Goldbach.PrimeWorld` already defines:

```lean
goldbachForbiddenResidues
goldbach_left_obstructed_iff
goldbach_right_obstructed_iff
goldbach_residue_eq_neg_iff
goldbach_card_forbidden
GoldbachResidueSurvives
goldbach_residue_periodic
goldbach_residue_insert
```

The source is
[PrimeWorld.lean](../../../DkMath/NumberTheory/Goldbach/PrimeWorld.lean:37).
The existing theorem `goldbach_residue_eq_neg_iff` already states that the two
raw classes merge iff `r ∣ 2 * n` (lines 60–68). CPG-V1-002 and CPG-V1-003
should therefore be typed bridges/phase observers over this layer, not a
second fixed-center residue implementation.

The production capacity facade records exact survivor/covered conservation and
the conditional equivalence with Strong Goldbach in
[Capacity.lean](../../../DkMath/NumberTheory/Goldbach/Capacity.lean:112).
The exact pair-overlap/Pascal residual ledger is in
[PairOverlap.lean](../../../DkMath/NumberTheory/Goldbach/PairOverlap.lean:169).

### 3.4 Existing one-sided prime-world refinement

`Primitive.PrimeWorldRefinement` provides the child coordinate

```lean
primeWorldChild S r j = r + j * primeWorldModulus S
```

and proves the zero-target wave theorem
`existsUnique_child_dvd_new_prime` together with the old-parent survival
split and the `q - 1` surviving-child cardinality. The source locations are
[PrimeWorldRefinement.lean](../../../DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean:128)
and lines 171–306.

This is not yet the Goldbach moving-wave theorem. Its target is
`q ∣ primeWorldChild S r j`, whereas Goldbach needs

```text
q ∣ n - (r + j*M)
q ∣ n + (r + j*M)
```

Consequently CPG-V1-004 requires the internal prerequisite `CPG-V1-004a`:
generalize the child observer to an arbitrary target congruence or establish
an equivalent `ZMod q` statement. Applying the zero-target theorem by an
unstated translation would be an invalid semantic shortcut.

### 3.5 Finite period/residue providers

`PeriodicPrimeWorld` proves product-period translation and centered mirror
invariance of the finite support observer. `PrimeWorldResidues` packages
canonical bounded residues and the refined-world equality. These are suitable
for synchronization and coordinate transport, but all conclusions remain
finite support/candidate statements.

### 3.6 Quadratic primitive audit already completed

`DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra` and its
`NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0` reports kernel-check
primitive/parity/support normalization, then conclude **Outcome B — structural
normalization only**. In particular, the restored-diagonal normalized capacity
criterion is equivalent to the existing `GoldbachCapacityEscape`.

This is why the present campaign does not repeat fixed-center primitive,
parity, LL/LR/RR, or static capacity normalization. The dynamic center/refinement
observer is a new research candidate, but it is not yet known to provide strict
information gain.

### 3.7 Projection prototype

`DkMath.Samples.Projection` contains `DkMath.Cosmic.Pi`, `U`,
`cosmicProjection_gap_eq`, and `cosmicProjection_mem_interval`. It is a sample
file, not a production `DkMath.CosmicFormula.Projection` owner. The `1/k`
bridge is therefore a downstream productionization task, not a current source
dependency.

### 3.8 Existing dynamic-phase analogue

`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport`
already has a square-anchor phase representative, period carry, moving center,
radius, plus/minus sheets, and successor laws. It is useful evidence that
finite phase transport can be packaged, but its semantics concern square-anchor
lift indices and `finitePrimeBasisProduct`, not Goldbach left/right obstruction
markers. It is a future bridge candidate only until an exact equivalence is
proved; it is not imported by the proposed Prime Gauge modules in the planning
pass.

## 4. Proposed implementation order

### CPG-V1-001 — CF2D return/congruence bridge

Freeze the minimal theorem statements over `regularKernel`:

```lean
regularKernel_pow_eq_one_iff_dvd
regularKernel_pow_eq_pow_iff_modEq
```

Use the audited `orderOf_dvd_iff_pow_eq_one` / `pow_eq_pow_iff_modEq` signatures
to select the `Nat.ModEq` orientation. Regress positive and boundary cases, including
`k = 2,3,5,6`, `n = 0,k,2*k,k+1`. Do not add a prime-order structure: exact
order of `regularKernel k` does not imply primality of `k`.

### CPG-V1-002 — Goldbach conjugate gauge bridge

Define only the smallest semantic pair/observer needed to express the existing
left/right residue classes with `regularKernel p`. Prefer the existing
`ZMod` theorems for the arithmetic proof and retain `u ≤ n` for natural
subtraction. Add raw gauge equivalences first; add proper wrappers only when
the endpoint inequality is explicit.

### CPG-V1-003 — center motion and relative phase

Prove marker successor and relative phase identities in the group/phase layer.
The identity `rho_p(n) = g_p^(2*n)` and its return condition are expected to be
static residue re-expression. This checkpoint must record that classification
unless it produces a genuinely new cross-fiber invariant.

### CPG-V1-004a / CPG-V1-004 — typed paired refinement

Before constructing left/right reserved children, freeze one of these equivalent
forms:

```text
Nat.ModEq q (r + j*M) a
ZMod q equality for the child target a
```

Then instantiate the targets `n` and `-n`, prove uniqueness for `j < q`, and
derive distinctness from `q ∤ 2*n`. Treat the `q-2` count as a local raw
cardinality statement only.

### CPG-V1-005 — parent-independent two-hole shape

The first research apex is:

```text
M * (jL - jR) ≡ 2*n [MOD q]
```

The theorem must state the exact index/subtraction bounds or use `ZMod q`.
It proves relative shape independence from the old parent only; it does not
prove an absolute child location or a surviving short-interval seat.

### CPG-V1-006 — cross-fiber transport

Prove the `n -> n+1` relative-shape step and any finite period law. Separate
center motion from seat motion, and record carry/boundary cases explicitly.

### CPG-V1-007 — information-gain audit and stop

Compare every new theorem against `Goldbach.PrimeWorld`,
`PrimeWorldResidues`, capacity, and the prior quadratic audit. Run bounded
Lean/scratch checks for uniqueness, distinctness, parent independence, center
transport, endpoint exceptions, and multi-`q` constraints. Classify the result:

```text
Outcome A: strict new finite information;
Outcome B: correct dynamic normal form but exact CRT/capacity re-expression;
Outcome C: a proposed invariant fails, with a minimal counterexample.
```

Do not proceed to a Goldbach proof campaign after Outcome B or C.

### CPG-V1-008 through CPG-V1-011 — downstream reusable layers

Only after the stop-gate record is accepted, implement finite family
synchronization, the minimal production Projection owner, modulus-to-mesh
identities, and finite grid approximation. An infinite density statement is a
separate campaign requiring an explicit growth provider.

## 5. Validation and documentation protocol

Each implementation checkpoint must have:

- a focused `lake build` from `lean/dk_math`;
- focused `DkMathTest` regressions for edge cases and counterexamples;
- a fresh warning scan independent of build success;
- an axiom/forbidden-construct audit in test or report scope;
- a numbered report under this directory;
- a source-accurate import/dependency note.

This report itself records only the pre-implementation replay. It does not
claim that any CPG-V1-001 or later theorem has been added.

## 6. Initial verdict

The workspace is ready for a narrow CPG-V1-001 implementation after roadmap
review. The first likely semantic blocker is not CF2D exact order, which is
already complete, but the target-generalization needed to turn the existing
zero-target prime-world refinement into a Goldbach paired moving-wave API.
