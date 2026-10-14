# NGEO-000 report — two-point gauge inventory and ownership boundary

## 1. Outcome

**Outcome A — inventory complete; the minimal v0 production architecture is
identified and frozen.**

This checkpoint is an audit, not NGEO-001 implementation.  The only file
added by this checkpoint is this report.  No existing production Lean module
was rewritten, and no prime, lattice, cyclotomic, FLT, unit-cycle, or phase
dependency was introduced.

## 2. Scope and repository state

The attached `instruction-000.md`, together with the checkpoint `README.md`
and `ROADMAP.md`, was treated as the bounded work contract.  The checkout was
already on:

```text
research/NumberGeometry-TwoPointGauge-260924-v0
```

The required audit targets were read in context:

```text
DkMath/SilverRatio/Sqrt2Lemmas.lean
DkMath/SilverRatio/SilverRatioCircle.lean
DkMath/SilverRatio/SilverRatioUnit.lean
DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
DkMath/Units/NPUnit.lean
DkMath/UnitCycle/Core.lean
DkMath/DHNT/UnitNatLayers.lean
```

The repository search also found two relevant existing bridges:

```text
DkMath/CosmicFormula/Rotation/CF2D/Topology.lean
DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
```

The latter already demonstrates that CF2D coordinates can be transported to
`EuclideanSpace ℝ (Fin 2)`, but it remains a CosmicFormula-owned bridge and is
not a reason for NumberGeometry to import the CF2D aggregate.

## 3. Existing API audit

### 3.1 Silver Ratio modules

`DkMath.SilverRatio.Sqrt2` owns the calibration constant
`sqrt2 := Real.sqrt 2`, with `sqrt2_sq`, `sqrt2_pos`, `sqrt2_ne_zero`, and
related radical identities.  These are useful for later examples but do not
define a generic point, vector, distance, or gauge.

`DkMath.SilverRatio.Circle` uses
`abbrev Point := ℝ × ℝ` and local coordinate definitions `add`, `sub`, and
`scale`.  Its `dist_sq` is the coordinate polynomial
`(p.1 - q.1)^2 + (p.2 - q.2)^2`; `concyclic4` is an existential equal-
`dist_sq` predicate, and `bcfg_concyclic` is a concrete White-Silver-Ratio
example.  This is a self-contained example layer, not a generic geometry
owner.  Its names and proof remain unchanged.

`DkMath.SilverRatio.Unit` owns the algebraic silver-ratio unit API:
`uAg`, `deltaAg`, `Ag`, `AgConj`, `AgNorm`, `Ag_mul`, `AgNorm_eq`, and
`AgNorm_mul`, together with the rational-coordinate uniqueness result.  The
word “norm” there is an algebraic conjugate norm and must not be reused as the
Euclidean pair-mass owner.

### 3.2 CF2D Basic and Euclidean bridges

`DkMath.CosmicFormula.Rotation.CF2D.Basic` owns:

```text
CF2D.Vec
CF2D.Vec.q2
CF2D.Vec.q2_mk
CF2D.Vec.q2_scale
CF2D.Vec.q2_star
CF2D.Vec.q2_conj
CF2D.UnitKernel.q2_act
CF2D.LevelSet
```

`Vec` has the intentionally CosmicFormula-specific `core`/`beam` fields and
the multiplicative `star` operation.  It does not provide the ordinary
additive/affine point interface needed for translation and arbitrary point
differences.  Therefore `q2`, `q2_scale`, `q2_star`, `q2_act`, and
`LevelSet` remain owned and unchanged by CF2D.

`CF2D.Topology` provides the coordinate bijection `Vec.toProd` /
`Vec.ofProd`; `CF2D.EuclideanPhase` provides `EuclideanPlane`,
`pairToEuclideanPlane`, `euclideanPlaneToPair`,
`pairToEuclideanPlane_norm_sq`, `Vec.q2_nonneg`,
`Vec.q2_eq_zero_iff`, `Vec.q2_pos_iff_ne_zero`, and the quarter-turn
`LinearIsometryEquiv`.  These are strong bridge precedents, but they remain
CF2D interpretation/rotation APIs rather than generic pair geometry.

The separate `CosmicFormula.Mass.Core` search result is also not a collision:
`MassSpace` stores a nonnegative rational-valued mass, while
`CosmicMassAPI` packages Big/Body/Gap/Core/Beam functions.  Neither is a
two-point Euclidean mass.

### 3.3 Unit and dynamic-layer modules

`DkMath.Units.NPUnit` defines the discrete phase object `NP`, constructors
`N`/`P`, the successor `succ`, and rational embedding `val`.  It is an
integer-plus-phase model, not a point representation or a real gauge.

`DkMath.UnitCycle.Core` owns the generic iteration abbreviation `iterate` and
the increment/no-cycle theorem families:

```text
I_iterate_of_unit
no_nontrivial_cycle_unit
I_iterate_of_u
cycle_mul_zero
no_nontrivial_cycle_of_pos_u
I_iterate_of_ge_one
no_nontrivial_cycle_of_ge_one
I_iterate_ge_sum_g
no_nontrivial_cycle_of_strict
```

`DkMath.DHNT.UnitNatLayers` packages these as `Progress`, `HasCycle`,
`Mixable`, and the bridge-shaped `Bridge`/`HasCycleOfUnit` API.  These are
appropriate future consumers of a proved discrete gauge transition, but they
do not define the continuous positive-real gauge and must not be imported by
the core geometry module.

## 4. Representation decision

### Option A — `CF2D.Vec ℝ`

This option has the best existing square-mass and multiplicative-action
surface: `q2`, `q2_scale`, `q2_star`, `UnitKernel.q2_act`, and `LevelSet` are
already checked.  Its costs are structural: the type is a bare structure,
its vocabulary is `core`/`beam`, and translation, subtraction, affine maps,
and standard inner-product lemmas are not its ownership.  Choosing it as the
NumberGeometry point type would either duplicate additive structure or force a
generic geometry facade to depend on CosmicFormula vocabulary.

**Decision:** retain as a later thin CF2D bridge; do not use as the v0 point
type.

### Option B — `ℝ × ℝ`

This matches `SilverRatio.Circle.Point` and makes coordinate examples short.
It also already has product additive operations, but the existing
`SilverRatio.Circle.add/sub/scale/dist_sq` are local definitions rather than a
generic theorem-owned interface.  It duplicates the coordinate square-mass
idea and makes standard finite-dimensional isometry reuse less direct.  A
coordinate pair can still be used at example boundaries through an explicit
equivalence.

**Decision:** retain for Silver-Ratio examples and bridges; do not make it the
primary v0 representation.

### Option C — `EuclideanSpace ℝ (Fin 2)`

This is mathlib's finite-dimensional L2 Euclidean space.  The checked API
includes:

```text
EuclideanSpace.real_norm_sq_eq
EuclideanSpace.dist_sq_eq
PiLp.inner_apply
EuclideanSpace.equiv
LinearIsometryEquiv
AffineIsometryEquiv
```

It gives ordinary subtraction, scalar multiplication, inner product, norm,
metric distance, and standard linear/affine isometry interfaces without a
custom similarity structure.  Coordinate recovery is explicit and stable via
`EuclideanSpace.equiv`; the existing CF2D bridge confirms the same conversion
pattern for `Fin 2`.

**Recommendation:** use

```lean
abbrev Point := EuclideanSpace ℝ (Fin 2)
```

in the future `DkMath.NumberGeometry.Basic` module.  Treat `Point` as the
vector-space model of affine `R^2`; use ordinary subtraction for point gaps.
This keeps the core independent of SilverRatio and CF2D while remaining
interoperable with both through explicit bridges.

## 5. Proposed production architecture

The proposed modules are deliberately future owners, not files implemented by
NGEO-000:

```text
DkMath.NumberGeometry.Basic
  Point := EuclideanSpace ℝ (Fin 2)
  pairVec / gap
  pairMass
  separated / Active
  pairMass_nonneg
  pairMass_eq_zero_iff
  pairMass_pos_iff_separated
  pairMass_self

DkMath.NumberGeometry.Gauge
  TwoPointKernel
  DistanceGauge / MassGauge
  OnNatShell
  normalized-mass lemmas under an active-base hypothesis

DkMath.NumberGeometry.Transport
  translation, linear-isometry, scaling, and explicit similarity transport

DkMath.NumberGeometry.LevelSet
  MassLevelSet, sharedPoint, and image/intersection transport

DkMath.NumberGeometry.Radical
  dot-product expansion and orthogonal radical landing

DkMath.NumberGeometry.Bridges
  later Silver/CF2D, prime-scale, UnitCycle, and 2p-phase adapters
```

The core imports should remain limited to the Euclidean-space, inner-product,
and affine-isometry mathlib material needed by the declarations.  It should
not import `DkMath.CosmicFormula`, `DkMath.SilverRatio`, `DkMath.Units`,
`DkMath.UnitCycle`, `DkMath.DHNT`, number theory, or FLT.

## 6. Required inventory table

| concept | existing owner/module | existing definition/theorem names | reuse status | missing theorem if any | proposed NumberGeometry owner |
|---|---|---|---|---|---|
| Point / Vec representation | CF2D Basic; SilverRatio Circle; mathlib | `CF2D.Vec`; `Circle.Point`; `EuclideanSpace ℝ (Fin 2)` | use EuclideanSpace as primary; bridge the other two | no generic point choice in DkMath | `NumberGeometry.Basic` |
| difference vector | mathlib additive/affine API | `sub`; `vsub`; `dist_eq_norm_sub`; `dist_eq_norm_vsub` | reuse unchanged | `pairVec` naming wrapper | `NumberGeometry.Basic` |
| pair square mass | CF2D Basic; SilverRatio Circle; mathlib | `Vec.q2`; `Circle.dist_sq`; `EuclideanSpace.real_norm_sq_eq` | preserve existing owners; define point-pair version once | `pairMass A B := ‖A - B‖ ^ 2` or real inner self | `NumberGeometry.Basic` |
| zero/separation criterion | CF2D EuclideanPhase; mathlib | `Vec.q2_eq_zero_iff`; `real_inner_self_pos`; `sub_eq_zero` | reuse proof shape, not namespace ownership | `pairMass_eq_zero_iff`; `pairMass_pos_iff_separated` | `NumberGeometry.Basic` |
| distance gauge | mathlib metric API | `dist`; `Metric.mem_sphere` | reuse unchanged | optional `DistanceGauge` alias | `NumberGeometry.Gauge` |
| mass gauge | no generic two-point owner | CF2D `q2` is vector mass, not pair mass | new generic definition | `MassGauge` / kernel target mass | `NumberGeometry.Gauge` |
| natural counting shell | no existing owner | none | new denominator-free predicate | `OnNatShell K n P` | `NumberGeometry.Gauge` |
| normalized mass | no existing two-point owner | quotient operations in mathlib only | deferred quotient view; not primitive | active-base quotient theorem | `NumberGeometry.Gauge` |
| translation invariance | mathlib affine/isometry API | `AffineIsometryEquiv.constVAdd`; `AffineIsometryEquiv.vaddConst`; `IsometryEquiv.vaddConst` | reuse transport facts | pair-mass translation corollary | `NumberGeometry.Transport` |
| orthogonal invariance | mathlib; CF2D Basic | `LinearIsometryEquiv`; `AffineIsometry.dist_map`; `UnitKernel.q2_act` | generic theorem new; CF2D theorem unchanged | `pairMass_linearIsometry` | `NumberGeometry.Transport` |
| scaling law | mathlib norm API | `norm_smul`; `EuclideanSpace.real_norm_sq_eq` | reuse algebraic norm facts | `pairMass_smul` | `NumberGeometry.Transport` |
| similarity transport | mathlib dilation/isometry infrastructure | `Dilation`; `Dilation.edist_eq`; `Dilation.mapsTo_sphere`; `AffineIsometryEquiv.map_vsub` | use explicit translation + scale + isometry first; avoid custom structure in v0 | `pairMass_similarity` and shell transport | `NumberGeometry.Transport` |
| mass level set | CF2D Basic / EuclideanPhase; mathlib | `CF2D.LevelSet`; `EuclideanCircleSq`; `Metric.sphere`; `EuclideanSpace.sphere_zero_eq` | new point-centered level set; bridge existing ones | `MassLevelSet A ρ` | `NumberGeometry.LevelSet` |
| shared-point transport | mathlib Set API | `Set.image_inter` for injective maps; `Equiv.image_inter` patterns | reuse set theorem | `sharedPoint_transport` | `NumberGeometry.LevelSet` |
| dot product | mathlib inner-product API | `⟪u, v⟫_ℝ`; `PiLp.inner_apply`; `real_inner_comm` | reuse unchanged | optional readable `dot` alias only if needed | `NumberGeometry.Radical` |
| radical q2 decomposition | CF2D polynomial proof shape; mathlib | `real_inner_add_add_self`; `real_inner_smul_left`; `real_inner_smul_right` | new generic inner-product theorem | `pairMass_radical_add` | `NumberGeometry.Radical` |
| radical landing by orthogonality | mathlib radical API | `Real.sq_sqrt`; `Real.sqrt_nonneg`; inner orthogonality | new theorem | `dot u v = 0 → ...` | `NumberGeometry.Radical` |
| gauge transition | no existing geometric owner | `UnitCycle.Core` has only Nat iteration | deferred until Gauge API | multiplicative `MassScalesBy` laws | `NumberGeometry.GaugeTransition` |
| prime-scale bridge boundary | Primitive/StructuralArithmetic later layer | `KnownPrimeScales`; `PrimeScaleGeneratedBy`; `Nat.Prime` | deferred bridge; no core import | `PrimeScaleStep` adapter | `NumberGeometry.PrimeScaleBridge` |
| UnitCycle bridge boundary | UnitCycle / DHNT | `iterate`; `I_iterate_of_u`; `Progress`; `Bridge` | deferred bridge; reuse no-cycle theorem ownership | positive gauge-cycle adapter | `NumberGeometry.UnitCycleBridge` |
| 2p phase bridge boundary | CF2D phase/rotation and later cyclotomic APIs | existing CF2D rotation/phase files; no generic NumberGeometry 2p owner | deferred downstream bridge | even/odd phase transport | `NumberGeometry.PhaseBridge` |

## 7. Core semantic decisions

### 7.1 Pair mass and GeoZero

The production definition should be a norm square or real inner self of the
ordinary point gap:

```lean
pairVec A B := B - A
pairMass A B := ‖pairVec A B‖ ^ 2
```

The equivalent inner-product form is available through
`real_inner_self_eq_norm_sq`.  The shortest robust proof path is:

```text
pairMass ≥ 0                       by norm_nonneg / inner_self_nonneg
pairMass = 0 ↔ B - A = 0          by real_inner_self_pos or sq_eq_zero
           ↔ A = B                by sub_eq_zero
pairMass > 0 ↔ A ≠ B              by real_inner_self_pos and sub_eq_zero
```

“GeoZero” and “GeoSucc” remain interpretation words.  No artificial
inductive point or Peano-style geometry type is justified.

### 7.2 Denominator-free shell API

For `K : TwoPointKernel`, the primary production predicate should be:

```lean
OnNatShell K n P : Prop :=
  pairMass K.source P = (n : ℝ) * pairMass K.source K.target
```

The cast of `n` to `ℝ` is explicit in the proposed type.  This yields shell 0
at the source and shell 1 at the target without a division side condition.
`NormalizedMass` is a secondary quotient view, used only with a theorem
hypothesis `pairMass K.source K.target ≠ 0` (or `K.Active`).

### 7.3 Similarity transport

Do not introduce a custom similarity record in v0.  First prove the small
family of gap/norm lemmas for

```text
P ↦ t + c • (R P)
```

where `R : Point ≃ₗᵢ[ℝ] Point`, `t : Point`, and `c : ℝ` (with `c ≠ 0` only
when an equivalence is required).  The proof shape is:

```text
(T P - T Q) = c • R (P - Q)
‖T P - T Q‖² = ‖c • R (P - Q)‖²
              = c² * ‖P - Q‖².
```

`AffineIsometryEquiv.map_vsub` and `AffineIsometry.dist_map` cover the
translation/orthogonal part; `norm_smul` covers the scale part.  mathlib's
`Dilation` API is a later abstraction option, but its `ℝ≥0` ratio and edistance
surface are not needed as the primitive v0 interface.

### 7.4 Level sets and intersections

Define a point-centered mass level set as:

```text
MassLevelSet A ρ := {P | pairMass A P = ρ}.
```

This keeps “circle” as an interpretation.  `Metric.sphere` and
`EuclideanSpace.sphere_zero_eq` can be used in a later positive-radius bridge.
For a bijective or injective transport map, `Set.image_inter` supplies the
set-theoretic intersection step; the NumberGeometry theorem should add only
the mass-level-set membership argument.

### 7.5 Radical landing

For `u v : Point`, `m : ℝ`, and `s = Real.sqrt m`, the future theorem should
be stated through the real inner product:

```text
⟪u + s • v, u + s • v⟫_ℝ
  = ⟪u,u⟫_ℝ + m * ⟪v,v⟫_ℝ + 2*s*⟪u,v⟫_ℝ
```

The orthogonality specialization follows from `⟪u,v⟫_ℝ = 0` and
`Real.sq_sqrt` under `0 ≤ m`.  The calibration `1² + (sqrt 2)² = 3` is an
example of this mechanism; it is not a classification theorem.

## 8. Ownership decisions for named existing declarations

| existing declaration | decision |
|---|---|
| `CF2D.Vec.q2` | existing theorem reused unchanged; no NumberGeometry alias as the core definition |
| `CF2D.Vec.q2_scale` | existing coordinate scaling theorem reused in a later CF2D bridge |
| `CF2D.Vec.q2_star` | existing CosmicFormula multiplication theorem; not a generic point-pair theorem |
| `CF2D.UnitKernel.q2_act` | existing unit-kernel action theorem; later orthogonal-transport bridge only |
| `CF2D.LevelSet` | existing vector level set remains CF2D-owned; NumberGeometry defines a point-centered mass level set separately |
| `SilverRatio.Circle.dist_sq` | existing coordinate specialization remains unchanged; later bridge may prove equality with generic `pairMass` |
| `SilverRatio.Circle.concyclic4` | existing example predicate remains unchanged; no generic circle ownership transfer |
| `SilverRatio.Circle.bcfg_concyclic` | example-only calibration theorem |

This separation preserves the useful mathematical distinction: CF2D owns
two-component multiplication and unit-kernel actions, while NumberGeometry
will own point-pair geometry and relative square-mass semantics.

## 9. Deferred boundaries

The following are explicitly outside NGEO-000 and must remain separate future
bridges:

- prime-scale steps, prime powers, or prime distribution;
- `PrimitiveSet`/finite-prime-world imports;
- UnitCycle or DHNT dynamic-unit realizations of a real gauge;
- logarithmic gauge coordinates;
- general `2p` phase and cyclotomic transport;
- Silver/Egyptian examples as foundations;
- any FLT, Goldbach, lattice, or global counting claim.

In particular, the existence of an `OnNatShell` predicate will be a relative
square-mass encoding only.  It does not provide existence of a point on every
shell, prime realization, or an arithmetic classification of shared points.

## 10. Validation

The audit used the current checked-out source and mathlib declarations named
above.  Since NGEO-000 adds documentation only, no new Lean declaration or
axiom audit is required.  The report itself is the requested deliverable.

The audited modules were checked with `lake build DkMath.SilverRatio.Sqrt2Lemmas DkMath.SilverRatio.SilverRatioCircle DkMath.SilverRatio.SilverRatioUnit DkMath.CosmicFormula.Rotation.CF2D.Basic DkMath.Units.NPUnit DkMath.UnitCycle.Core DkMath.DHNT.UnitNatLayers`; the focused build completed successfully (`8931` jobs).  `git diff --check` and `git diff --no-index --check /dev/null <report-000.md>` completed without whitespace diagnostics.
