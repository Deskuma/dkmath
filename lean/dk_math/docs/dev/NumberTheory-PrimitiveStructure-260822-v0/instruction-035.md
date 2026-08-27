# Codex Instruction — PRIM-FD-000 Finite-Difference Invariant / Square-Body Conservation Audit

Branch: `wip/number-theory-primitive-structure-260822-v2`

Project: DkMath NumberTheory Primitive Structure / Legendre first application

Environment: keep the current Lean / Mathlib v4.32.2 toolchain. Do **not** upgrade to v4.33.0 in this checkpoint.

## Checkpoint type

This is a **read-only mathematical and API reconnaissance**.

Do not modify Lean source files, imports, dependencies, `lean-toolchain`, Lake configuration, PRIM-C001/C002, PRIM-L022, the Legendre facade/frontier, or existing CosmicFormula modules.

Produce only the requested report.

---

# 1. Current state and reason for this audit

Two recent reconnaissance routes have now stopped at structural-but-noncontradictory refinements:

```text
PRIM-PAR-000
  Outcome B — LOSSLESS COORDINATE

PRIM-L023
  Outcome B — STRUCTURAL REFINEMENT
```

The current exact Legendre frontier remains

```text
∀ n > 0, ¬ SquareOffsetsFullyCovered n.
```

The finite arithmetic stack already contains:

```text
finite prime worlds / residue refinement
square-wave exact counts and carries
pair-overlap ledgers
coprime packets
quotient Direction/Depth classification
localized obstruction ledgers
packet cross-factor coprimality
unit-residue factor rectangles
square-Body old-generated / unique-fresh × small-cofactor normal form
```

Neither local exponent parity nor the packet O/F branch matrix currently gives a new full-cover obstruction.

A separate DkMath source family already formalizes a finite-difference viewpoint. The purpose of PRIM-FD-000 is to determine whether that existing source contains a **concrete arithmetic invariant** that is absent from the current unit-one Legendre framework and that could plausibly constrain full cover.

Do not build a continuous-analysis abstraction merely because the files exist.

---

# 2. Existing source assets that must be audited

At minimum inspect the current declarations and theorem ownership in:

```text
DkMath/CosmicFormula/CosmicDifferenceKernel.lean
DkMath/CosmicFormula/CosmicDerivativeBasic.lean
DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean
DkMath/CosmicFormula/CosmicFormulaDerivativeBridge.lean
DkMath/Analysis/TaylorBridge.lean
DkMath/CosmicFormula/CosmicFormulaBasic.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean
```

Also inspect the relevant current Primitive / Legendre owners:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/Wave.lean
DkMath/NumberTheory/Legendre/SmallCofactor.lean
DkMath/NumberTheory/Legendre/Frontier.lean
```

Use existing repository documentation only as secondary context. The actual Lean declarations are authoritative for what is currently available.

---

# 3. Mathematical source picture to test

The current real finite-difference API already contains

```text
delta f x u = f(x+u) - f(x)
cosmicKernel f x u = delta f x u / u
```

and the discrete product rule / linearity laws.

For the square function, the derivative bridge currently exposes identities of the form

```text
delta(y ↦ y^2) x u = u * powerKernel 2 x u

cosmic_formula_unit x u
  = u * (powerKernel 2 x u - 2*x)
  = u^2.
```

The conceptual finite-difference square identity is

```text
(x+u)^2 - x^2 = u * (2*x + u).
```

For `u ≠ 0`, the difference quotient is therefore

```text
K_2(x,u) = 2*x + u.
```

The unit-one Legendre shell is the specialization `u = 1`:

```text
(n+1)^2 - n^2 = 2*n + 1.
```

The audit must test whether keeping `u ≠ 0` before specializing to `u = 1` exposes any invariant or conservation law that genuinely adds information to the current finite prime-wave formulation.

---

# 4. Mandatory audit questions

## Q1 — exact finite-difference theorem inventory

List the smallest existing theorem chain for the square function that gives, or nearly gives,

```text
delta(square) x u = u * (2*x + u)
```

and, under `u ≠ 0`,

```text
cosmicKernel(square) x u = 2*x + u.
```

Classify each desired statement as:

```text
A. exact theorem already exists
B. immediate thin consequence exists
C. genuinely missing
```

Do not implement the missing statement in this checkpoint.

## Q2 — Big / Body / Gap finite-difference conservation

Using the existing Cosmic Formula square family, identify the exact algebraic relationships among

```text
Big(x,u)  = (x+u)^2
Body(x,u) = x*(x+2*u)
Gap(u)    = u^2
```

and their finite differences with respect to the relevant variable(s).

Test separately:

```text
A. vary x with u fixed
B. vary u with x fixed
```

For each variation, record whether the difference law gives:

- an `x`-independent conserved quantity;
- a `u`-independent conserved quantity;
- a constant second difference;
- only a restatement of the original quadratic identity.

The report must distinguish an actual invariant from an algebraic tautology.

## Q3 — zero-difference / derivative limit versus finite information

Audit the existing derivative-limit bridge.

Determine exactly what information survives when the finite increment tends to zero, and what information is lost relative to the nonzero-`u` identity.

In particular answer:

```text
Does the derivative recover only the linear term 2*x,
or is there an additional finite-u remainder/invariant that survives as a reusable theorem?
```

Do not assume that taking a derivative strengthens the discrete theorem.

## Q4 — unit-one specialization and Legendre shell

Write the exact specialization path from the generic finite-difference square identity to

```text
(n+1)^2 - n^2 = 2*n + 1
```

and to the current Legendre offset body

```text
n^2 + r,  1 ≤ r ≤ 2*n.
```

Determine whether the current Legendre modules have already encoded all arithmetic information contained in this specialization.

A useful answer must explicitly compare the finite-difference data with current objects such as:

```text
SquareOffset
squareOffsets
squareWaveOffsets
squareWaveCarry
SquareOffsetsFullyCovered
```

## Q5 — prime-wave interaction test

This is the main leverage question.

Search for a concrete theorem path from a finite-difference identity to **divisibility/residue/support information**.

For example, test whether any existing result can turn a relation such as

```text
(n+u)^2 - n^2 = u*(2*n+u)
```

into a new restriction on simultaneous old-prime wave coverage of the intermediate shell.

Possible useful outputs would include, but are not limited to:

```text
- a conserved residue quantity across the shell;
- an exact relation between wave carries at adjacent anchors;
- a finite-difference identity for coverage multiplicity;
- a forced imbalance between left/right or old/fresh packet data;
- a monotone or telescoping quantity under n ↦ n+1;
- a strict bound on a full-cover ledger that is not already present.
```

Do not infer any of these from analogy. Identify an actual theorem chain or classify the bridge as missing.

## Q6 — second-difference / constant-curvature test

The square sequence has constant second finite difference.

Audit whether the existing DkMath finite-difference API can express this cleanly, and then test whether

```text
Δ²(n ↦ n²) = 2
```

has any nontrivial interaction with:

```text
prime-world modulus
square-wave forbidden residues
wave carry
packet determinant n
small-cofactor return
```

A constant second difference by itself is not a number-theoretic obstruction. The report must identify a concrete consumer or classify it as geometric bookkeeping only.

## Q7 — relation to C001/C002 and L022

Test whether the finite-difference square family adds anything to the generic factor normal form

```text
m ≤ (P+1)^2 - 1
→ old-generated
  or unique fresh ℓ > P × small k ≤ P.
```

In particular ask whether varying the shell parameter can relate the fresh/small decomposition at anchor `P` to the decomposition at another anchor.

Do **not** call `k ≤ P` a descent unless a smaller state, reconstruction theorem, preserved hypotheses, and strict measure are all present.

## Q8 — exact leverage against full cover

Attempt to identify at least one candidate statement of the form

```text
SquareOffsetsFullyCovered n
→ NEW CONSTRAINT(n)
```

where `NEW CONSTRAINT` is not merely:

- the existing wave-count identity;
- the existing carry identity;
- the existing pair-overlap ledger;
- the existing packet determinant;
- the existing O/F branch matrix;
- a rewrite of `(n+1)^2 - n^2 = 2*n+1`.

If no such statement exists in the current theorem graph, say so explicitly.

---

# 5. Required outcome classification

Choose exactly one final classification.

## Outcome A — DIRECT INVARIANT LEVERAGE

Use only if the audit identifies a concrete finite-difference-derived invariant that yields a genuinely new constraint on `SquareOffsetsFullyCovered n` or one of its existing obstruction ledgers.

The report must state the exact theorem chain and the smallest proposed next Lean checkpoint.

## Outcome B — ALGEBRAIC / GEOMETRIC REFINEMENT

Use if the finite-difference viewpoint gives a cleaner conserved-coordinate or second-difference formulation, but no new full-cover restriction.

In this case recommend stopping the route unless a future concrete consumer appears.

## Outcome C — REDUNDANT SPECIALIZATION

Use if the current unit-one Legendre framework already contains all relevant finite information and the derivative / finite-difference layer only rewrites existing square identities without adding a useful coordinate.

In this case explicitly close the route for the present Legendre project.

---

# 6. Required report

Create only:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-finite-difference-invariant-audit-260825.md
```

The report must contain:

1. executive outcome;
2. exact theorem inventory with source modules;
3. Q1–Q8 answers;
4. a table separating finite-`u` information, derivative-limit information, and unit-one information;
5. exact interaction, if any, with current Legendre objects;
6. explicit list of tempting but invalid inferences;
7. final recommendation on whether a Lean implementation checkpoint is justified.

---

# 7. Invalid inferences to guard against

Do not claim any of the following without a theorem:

```text
u > 0 finite difference ⇒ prime escape
constant second difference ⇒ prime in every square shell
derivative conservation ⇒ residue conservation
u → 0 limit ⇒ stronger discrete information
continuous invariant ⇒ finite prime-wave imbalance
finite-difference identity ⇒ full-cover contradiction
small-cofactor return ⇒ recursive descent
```

Also do not identify a real-variable derivative statement with a natural-number divisibility theorem without an explicit bridge.

---

# 8. Dependency / implementation restrictions

Do not add:

- a new `CosmicDifference` abstraction;
- a new derivative namespace;
- a new Legendre continuous model;
- a real/complex dependency into `NumberTheory/Primitive` merely for this audit;
- RH/CFBRC dependencies;
- `ZMod` machinery;
- analytic prime estimates;
- a new full-cover provider assumption;
- any proof of Legendre's conjecture.

Keep Mathlib at v4.32.2.

---

# 9. Verification

Because this checkpoint is report-only:

```sh
git diff --check
```

and perform whitespace / placeholder audits on the new report.

Do not run Lean builds merely for a documentation-only checkpoint unless the reconnaissance itself requires an interactive `#check` or temporary local scratch test. Any scratch file must not be committed.

---

# 10. Stop condition

Do **not** start a subsequent implementation checkpoint automatically.

If the outcome is B or C, stop this finite-difference route and report that no implementation is justified.

If the outcome is A, report the exact minimal theorem surface that would constitute the next checkpoint, but do not implement it until review.