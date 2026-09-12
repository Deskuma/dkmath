# CPG-V1-007 — information-gain audit

Date: 2026-09-12  
Status: complete — Outcome B

## Verdict

```text
Outcome B — STRUCTURAL NORMALIZATION / TRANSPORT ONLY

The dynamic CF2D/PrimeGauge layer gives a faithful and reusable
phase-coordinate model of the existing Goldbach residue/refinement
arithmetic, including a parent-independent relative shape and cross-fiber
successor law.

It does not presently reduce the actual interval cover, control proper
endpoint obstruction, or force an interval survivor. No strict Goldbach
information gain is established.
```

The Goldbach proof campaign therefore closes at CPG-V1-007. This is a scope
verdict, not a failure of the finite API: the CPG-V1-001--006 spine remains
available for separately scoped reusable coordinate work.

## 1. Derivability and dependency audit

The source imports and proof bodies were checked against the existing owners.
The following is the source-accurate dependency map; a conceptual comparison
is not described as a direct import when the file does not import that module.

| Layer | Current owner and actual relation | Information classification |
|---|---|---|
| CPG-V1-001 | `PrimeGauge/Return.lean` imports `CF2D.CycleDivision` and proves the exact-order return/congruence wrappers. | CF2D-to-return normalization. |
| CPG-V1-002/003 | `PrimeGauge/GoldbachPhase.lean` imports `Goldbach.PrimeWorld` and `PrimeGauge.Return`; its marker, center, and relative-phase laws are residue/algebra bridges. | Gauge and phase reformulation. |
| CPG-V1-004a | `Primitive/PrimeWorldRefinement.lean` imports `Primitive.PeriodicPrimeWorld`; `existsUnique_child_eq_target` is the affine CRT target-coordinate bijection for a fresh prime. | Finite target transport; every `ZMod q` target is realized. |
| CPG-V1-004--006 | `PrimeGauge/GoldbachRefinement.lean` imports `Goldbach.PrimeWorld`, `PrimeGauge.GoldbachPhase`, and `Primitive.PrimeWorldRefinement`. The `q-2` count, CPG-V1-005 shape, and CPG-V1-006 successor law are obtained by target-set transport and ring subtraction. | Child-index coordinate normalization/transport. |
| Existing periodic provider | `Primitive/PeriodicPrimeWorld.lean` supplies product-period invariance and centered/reflected support-disjointness. | Periodic finite observer. |
| Existing residue provider | `Goldbach/PrimeWorld.lean` supplies `{+n,-n}`, the merge criterion `q ∣ 2*n`, CRT representatives, and local survivor counts. | Existing residue/CRT arithmetic. |
| Capacity comparator | `Goldbach/Capacity.lean` defines actual interval seats, proper obstruction, exact covered/survivor conservation, and `GoldbachCapacityEscape`. It is an audit comparator, not imported by `GoldbachRefinement.lean`. | Actual interval capacity. |
| Pair-overlap comparator | `Goldbach/PairOverlap.lean` counts actual proper-obstruction overlap and proves the exact Pascal residual decomposition. It is an audit comparator, not imported by `GoldbachRefinement.lean`. | Existing actual-seat overlap ledger. |

In particular, CPG-V1-005 is the linear elimination of the two equations
`r + jL*M = n` and `r + jR*M = -n` in `ZMod q`. CPG-V1-006 applies that
identity at `n` and `n+1` and subtracts. Neither theorem adds a restriction on
the center. CPG-V1-004a explains why: after the fresh-prime coprimality
hypothesis, the affine child map realizes every target class.

## 2. Bounded phase/interval countermodel

The audit scratch
[cpg-v1-007-countermodel.lean](verification/cpg-v1-007-countermodel.lean)
imports the relevant production APIs but defines no production declaration.
It kernel-checks:

```text
S = {2, 3, 5},  M = 30,  q = 7,  n = 10,  r = 29
children = 29, 59, 89, 119, ...
card (pairedSurvivingChildIndices 10 S 7 29) = 5 = q - 2
```

It also checks that filtering those phase-surviving indices by the actual
Goldbach offset interval gives the empty set:

```lean
phaseSurvivorsWithinGoldbachOffsets 10 S 7 29 = ∅
```

Here `goldbachOffsets 10 = Finset.range 9`, while every displayed affine child
value is already at least `29`. Thus phase survivor existence does not imply
that an affine child lands in the actual interval seat set. This is a bounded
countermodel to the proposed bridge, not a claim that the complete Goldbach
interval for `n = 10` has no survivor.

## 3. Capacity and PairOverlap audit

The actual interval layer in `Goldbach/Capacity.lean` uses
`goldbachOffsets`, `GoldbachProperObstructed`, and the exact identity

```lean
goldbachPairAt_iff_covered_card_lt
```

together with `GoldbachCapacityEscape`. Its available residue-capacity result
is an upper bound on `goldbachBlockedSeats`, and its exact conservation theorem
still counts actual interval seats. No theorem in the CPG-V1-001--006 chain
supplies the required weaker hypothesis
`covered.card < n - 1`, nor an actual `GoldbachSurvives` offset.

`Goldbach/PairOverlap.lean` independently retains actual proper-obstruction
support and proves

```lean
goldbachPrimePairOverlapCount n =
  goldbachOverlapExcess n + goldbachPairOverlapResidual n
```

The CPG phase layer has no theorem connecting its one-direction `q-2` phase
survivors to cross-prime overlap among actual short-interval seats. Therefore
it contributes no new capacity pressure over the existing ledger.

## 4. Validation

The production chain was already validated through CPG-V1-006. The audit
scratch was executed from `lean/dk_math` with:

```bash
lake env lean \
  docs/dev/cf2d-prime-gauge-projection-260911/verification/cpg-v1-007-countermodel.lean
```

Result: exit 0. The scratch has no `sorry`, `admit`, user `axiom`, `unsafe`,
or `native_decide` construct. `git diff --check` also passes for the current
workspace changes.

## Roadmap transition

CPG-V1-007 is complete with Outcome B. No further Goldbach production theorem
is authorized by this route. CPG-V1-008 and later Projection/continuum work
remain separately scoped reusable-API research and must not be presented as a
Goldbach proof provider.
