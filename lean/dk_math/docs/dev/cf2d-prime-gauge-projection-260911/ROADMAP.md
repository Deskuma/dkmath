# ROADMAP — CF2D / Prime Gauge / Goldbach Dynamic Phase / Cosmic Projection / Continuum v1

Date: 2026-09-12  
Branch: `wip/cf2d-prime-gauge-projection-260911-v1`  
Base: `develop`  
Status: CPG-V1-010 complete as independent finite geometry/API work; the next
source milestone is CPG-V1-011.

## 0. Current campaign state

`CPG-V1-000` repository-first audit, the first three thin bridges, the typed
target-congruence prerequisite, the paired phase refinement, the
parent-independent relative-shape identity, and its cross-fiber successor law
are complete. The information-gain audit found no strict reduction of the
actual interval-capacity problem. CPG-V1-008 now adds the independent finite
prime-family synchronization core.
The current workspace has the
CF2D exact-order provider, finite prime-world periodic/refinement providers,
the Goldbach fixed-center paired-residue/capacity layers, and the new Prime
Gauge return/Goldbach phase modules.

The first implementation target is the finite, kernel-checked bridge:

```text
CF2D exact order
-> return / phase equality
-> Goldbach left-right conjugate gauge
-> center and relative-phase dynamics
-> typed paired fresh-prime refinement
-> parent-independent two-hole shape
-> cross-fiber transport
-> information-gain audit
```

`CPG-V1-007` was the mandatory stop gate. Projection, mesh, and continuum work
remain downstream and must not be used as a Goldbach proof provider for this
route after the dynamic-phase information-gain verdict.
CPG-V1-009 and CPG-V1-010 now provide the finite Projection/CF2D coordinate and
world-modulus mesh layers.

## 1. Scope contract

### User-requested work completed by this planning pass

- Inspect the workspace before implementation.
- Fix the current source/API/import boundaries.
- Prepare a staged implementation plan and roadmap management artifact.
- Place the work report under this directory.

### Attached-document material retained as design constraints

- The attached document is an implementation plan and research boundary, not
  an unconditional command to implement every listed candidate theorem.
- Its `CPG-V1-000` audit and `CPG-V1-007` information-gain stop are retained.
- Its non-goals are retained: no Strong Goldbach, Twin Prime, Legendre, RH,
  prime-existence, universal escape, or continuum prime-realization claim.
- Static fixed-center normalization is not repeated after the audited Outcome B
  result.

## 2. Milestones and gates

| ID | Status | Deliverable | Required evidence / exit condition |
|---|---|---|---|
| CPG-V1-000 | complete | Repository-first audit | Current declarations, imports, branch, and focused replay recorded in `report-000.md`. |
| CPG-V1-001 | complete | CF2D return and congruence bridge | `Return.lean` proves both bridges; focused production/test build and axiom/forbidden-construct checks passed. |
| CPG-V1-002 | complete | Goldbach conjugate gauge bridge | `GoldbachPhase.lean` bridges raw left/right `ZMod` obstruction to equality/conjugacy of CF2D markers; focused build and audits recorded in `report-002.md`. |
| CPG-V1-003 | complete | Center motion and relative phase | `GoldbachPhase.lean` proves marker successor, double-center relative phase, return/divisibility, and relative successor laws; focused build and audits recorded in `report-003.md`. |
| CPG-V1-004a | complete | Target-congruence child prerequisite | `PrimeWorldRefinement.lean` proves `existsUnique_child_eq_target` for arbitrary `a : ZMod q`; focused build and audits recorded in `report-004a.md`. |
| CPG-V1-004 | complete | Paired fresh-prime refinement | `GoldbachRefinement.lean` proves left/right target uniqueness, distinctness under `q ∤ 2*n`, and the `q-2` phase-level surviving-child count; interval/raw endpoint filtering remains separate. |
| CPG-V1-005 | complete | Parent-independent two-hole shape | `GoldbachRefinement.lean` proves the requested `ZMod q` identity from the two child target equations; focused build and audits recorded in `report-005.md`. |
| CPG-V1-006 | complete | Cross-fiber center transport | `GoldbachRefinement.lean` proves the successor law `Δ(relative shape) * M = 2`; focused build and audits recorded in `report-006.md`. |
| CPG-V1-007 | complete — Outcome B | Information-gain audit | Dependency/derivability audit, bounded Lean countermodel, and Capacity/PairOverlap comparison recorded in `report-007.md`; no strict Goldbach information gain. |
| CPG-V1-008 | complete | Finite prime-family synchronization | `PrimeGauge/PrimorialSync.lean` proves family-wide return iff world-modulus divisibility and least-positive synchronization; focused build and audits recorded in `report-008.md`. |
| CPG-V1-009 | complete | Production Projection API and CF2D bridge | `CosmicFormula/Projection/Basic.lean` and `CF2DBridge.lean` own the minimal `Pi`/`U` algebra and `1/k` bridge; focused build and audits are recorded in `report-009.md`. |
| CPG-V1-010 | complete | World-modulus projection and mesh | `Projection/WorldModulus.lean` proves the `1/M` projection gap and fresh-prime mesh refinement; focused build and audits are recorded in `report-010.md`. |
| CPG-V1-011 | deferred | Finite normalized grid | Prove finite `1/k` approximation; any infinite density theorem requires a separately identified growth provider. |

`queued` means planned but not started; `deferred` means intentionally held
behind the dynamic-phase stop gate or retained only as an independent API
research possibility after Outcome B. These are roadmap labels, not Lean
propositions.

## 3. Ownership and import policy

The planned production surface is intentionally thin:

```text
DkMath/CosmicFormula/Projection/
  Basic.lean
  CF2DBridge.lean
  WorldModulus.lean

DkMath/NumberTheory/PrimeGauge/
  Return.lean
  GoldbachPhase.lean
  GoldbachRefinement.lean
  PrimorialSync.lean
  ContinuumGrid.lean
```

Create a file only when a stable public boundary exists. Candidate import
owners are:

- `CF2D.CycleDivision` / `CF2D.RegularOrbit` for the exact finite orbit;
- `Goldbach.PrimeWorld` for existing `ZMod` left/right residue semantics;
- `Primitive.PrimeWorldRefinement` for old-world child coordinates and fresh
  prime hypotheses;
- `PeriodicPrimeWorld` / `PrimeWorldResidues` for period and canonical residue
  semantics;
- `Samples.Projection` only as a source audit, never as a production dependency;
- `PrimorialUniverse.SquareAnchorPhaseSuccessorTransport` only as a separately
  audited pattern. Its square-anchor center/radius semantics are not silently
  identified with Goldbach markers.

Do not add a new top-level aggregator until the corresponding modules have
focused builds and a public import audit. Do not add `PrimeGauge` structures
when theorem/docstring wrappers express the same existing mathematics.

## 4. Implementation protocol

For each queued milestone:

1. Freeze the statement and namespace from the current source audit.
2. Implement the smallest typed bridge, with natural subtraction bounds made
   explicit or with `Nat.ModEq`/`ZMod` used as the intermediate language.
3. Add a focused regression in `DkMathTest` and keep research scratch separate
   from the production facade.
4. Run the narrow module build from `lean/dk_math` and inspect the fresh log for
   errors and warnings.
5. Run a forbidden-construct/axiom audit appropriate to the checkpoint.
6. Record the exact result in a numbered report before advancing the roadmap.

The paired refinement implementation must first settle whether its child
observer is stated in `Nat.ModEq` or `ZMod`. The choice is part of CPG-V1-004a,
not an assumption carried into production files.

## 5. Mandatory semantic barriers

The following statements remain outside the campaign's proof claims:

```text
exact order of regularKernel k -> primality of k
phase/residue equivalence -> new Goldbach information
q-2 children -> short-interval survivor
finite synchronization -> existence of a new prime
dense normalized grid -> prime in every interval
Projection boundary completion -> integer prime realization
any finite observer identity -> Strong Goldbach / Twin Prime / Legendre / RH
```

The words `candidate seat`, `raw obstruction`, `proper obstruction`, and
`survivor` must remain distinct in definitions and docstrings.

## 6. Post-verdict boundary

`CPG-V1-007` closes the Goldbach proof campaign for this route with Outcome B:
structural normalization / transport only. The target-congruence prerequisite
is available as
`existsUnique_child_eq_target`; CPG-V1-004 packages its two `ZMod q` targets,
and CPG-V1-005/006 record their parent-independent relative shape and
successor law. The existing zero-target theorem and interval endpoint
conditions remain separate compatibility providers, and neither phase identity
nor cardinality theorem is a proof of the Goldbach moving-wave statement.

CPG-V1-008 is complete as independent reusable-API work, CPG-V1-009 is complete
as independent Projection/CF2D geometry/API work, and CPG-V1-010 is complete as
independent finite world-modulus mesh work. The next source milestone is
CPG-V1-011, finite normalized grid. These items remain separate from
interval/prime realization and do not provide a continuum prime claim.
