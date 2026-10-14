# NGEO-006 — Silver / Egyptian calibration bridges

You are implementing checkpoint NGEO-006 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-005.md

lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/Transport.lean
lean/dk_math/DkMath/NumberGeometry/LevelSet.lean
lean/dk_math/DkMath/NumberGeometry/Radical.lean

lean/dk_math/DkMath/SilverRatio/Sqrt2Lemmas.lean
lean/dk_math/DkMath/SilverRatio/SilverRatioCircle.lean

Journal/260724-1200-four-points-share-a-circle-by-squared-distance.md
docs/BookOfMagic/0002_白銀円環と鍵石N.md
~~~

NGEO-005 established the generic radical landing mechanism:

~~~text
||u + sqrt(m) v||^2
  = ||u||^2 + m ||v||^2 + 2 sqrt(m) <u,v>

<u,v> = 0
  -> radical cross term disappears.
~~~

NGEO-006 is a calibration checkpoint. Its job is to connect the generic
NumberGeometry API to selected existing Silver-ratio and Egyptian-circle
examples without changing theorem ownership in the old modules.

## Objective

Produce thin, checked bridges showing that the earlier coordinate geometry is
an instance of the new NumberGeometry square-mass language.

Track A is the exact SilverRatio bridge.

Track B is a conservative Egyptian calibration that formalizes only exact
algebraic claims supported by checked sources or explicitly defined points.

The report must clearly distinguish:

~~~text
LEAN-CONFIRMED
EXACT-CALIBRATION
RESEARCH-OBSERVATION
DEFERRED
~~~

Do not silently promote a GeoGebra numerical observation or a draft document
formula into a production theorem.

## Production layout

Prefer:

~~~text
lean/dk_math/DkMath/NumberGeometry/Bridge/SilverRatio.lean
lean/dk_math/DkMath/NumberGeometry/Examples/EgyptianCircle.lean
~~~

A different thin split is acceptable if repository conventions strongly favor
it.

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

only for modules intended as public NumberGeometry surface.

Do not wholesale refactor the old SilverRatio modules.

## 1. Coordinate bridge: real pair to NumberGeometry.Point

Define one explicit conversion from a pair of reals to:

~~~lean
Point := EuclideanSpace ℝ (Fin 2)
~~~

Preferred conceptual form:

~~~lean
def ofPair (p : ℝ × ℝ) : Point := ...
~~~

or a bridge-local SilverRatio-qualified equivalent.

Inspect Mathlib and existing DkMath bridges first. Reuse EuclideanSpace.equiv or
an existing pair-to-Euclidean bridge if appropriate.

Required: coordinate order must be explicit and stable.

Do not create multiple competing conversion functions.

## 2. Squared-distance bridge

Prove the exact identity:

~~~text
pairMass (ofPair p) (ofPair q)
  = DkMath.SilverRatio.Circle.dist_sq p q.
~~~

Suggested theorem name:

~~~text
pairMass_ofPair_eq_dist_sq
~~~

This theorem is central to NGEO-006.

Coordinate expansion is allowed in this bridge file, but must not leak back
into NumberGeometry core.

## 3. SilverRatio four-point calibration

Reuse the existing checked theorem:

~~~text
DkMath.SilverRatio.Circle.bcfg_concyclic
~~~

Do not re-prove its coordinate algebra from scratch.

Convert its witness into NumberGeometry language.

Preferred theorem shape:

~~~lean
theorem bcfg_common_massLevel :
  ∃ (O' : Point) (rho : ℝ),
    ofPair Circle.B ∈ MassLevelSet O' rho ∧
    ofPair Circle.C ∈ MassLevelSet O' rho ∧
    ofPair Circle.F ∈ MassLevelSet O' rho ∧
    ofPair Circle.G ∈ MassLevelSet O' rho
~~~

If the exact center is naturally ofPair Circle.O, prove the stronger calibrated
form using that center.

Do not define a second generic concyclic4 predicate unless absolutely needed.

## 4. Exact common Silver mass, if cheap

The existing theorem chooses the squared radius as dist_sq O B.

If it is cheap, prove the exact closed form from checked definitions.

The campaign analysis expects a value algebraically equivalent to:

~~~text
3 - 3*sqrt(2)/2
~~~

but do not hard-code that as fact without a Lean proof.

If the closed form is not cheap, keep the common-level theorem and defer the
closed form.

## 5. Egyptian mass-3 calibration

Define exact EuclideanSpace points cleanly.

At minimum use an origin and orthogonal unit coordinate directions.

Calibrate the point equivalent to:

~~~text
W = (1, sqrt(2))
~~~

and prove:

~~~text
pairMass origin W = 3.
~~~

Prefer proving this as a direct instance of the NGEO-005 theorem:

~~~text
pairMass_radical_of_inner_eq_zero
~~~

with:

~~~text
u = x unit direction
v = y unit direction
m = 2
<u,v> = 0.
~~~

Use the existing checked sqrt-two identity from:

~~~text
DkMath.SilverRatio.Sqrt2.sqrt2_sq
~~~

only where needed.

This theorem is the exact mathematical content of the observed sqrt(3)-radius
layer:

~~~text
distance(origin,W)^2 = 3.
~~~

An unsquared theorem distance = sqrt(3) is optional and may be deferred.

## 6. Radius 3 / mass 9 calibration

The repository BookOfMagic source records a measuring circle centered at the
origin with radius 3.

Add a simple exact calibration point:

~~~text
R = (3,0)
pairMass origin R = 9.
~~~

This provides the checked pair:

~~~text
sqrt(3)-distance layer -> mass 3
3-distance layer       -> mass 9.
~~~

Do not claim this alone proves all incidences of a particular GeoGebra file.

## 7. Keystone N bounded optional target

The BookOfMagic draft records:

~~~text
N = (2 - sqrt(2)/2, 2 + sqrt(2)/2)
q2(N) = 9.
~~~

If small, formalize:

~~~text
pairMass origin keyN = 9.
~~~

Optionally also prove:

~~~text
x(keyN) + y(keyN) = 4.
~~~

Do not implement the full uniqueness theorem unless it is clearly tiny.

Full Keystone-N uniqueness is not required for NGEO-006.

## 8. MassLevelSet calibration

Where cheap, express exact points by membership:

~~~text
W ∈ MassLevelSet origin 3
R ∈ MassLevelSet origin 9.
~~~

For SilverRatio, the four old points should appear as members of one common
MassLevelSet.

Do not infer new shared-point incidences that are not proved.

## 9. Evidence discipline

The report must classify each relevant claim.

Examples:

- Existing bcfg_concyclic: LEAN-CONFIRMED before NGEO-006.
- New pairMass origin W = 3: LEAN-CONFIRMED after proof.
- A GeoGebra object numerically near (1,sqrt(2)): RESEARCH-OBSERVATION unless
  its construction is formally identified with the exact point.
- Formulae in BookOfMagic marked Draft: source material, not automatically Lean
  theorems.
- Any intended but unproved incidence: DEFERRED.

The user supplied GeoGebra research that motivated the mass-3 and mass-9
layers, but this checkpoint must formalize exact statements rather than numeric
coincidence.

## 10. No historical claims

The BookOfMagic document distinguishes the Rhind Papyrus calculation from
modern grid/octagonal reconstruction.

NGEO-006 is mathematical calibration only.

Do not add claims about ancient Egyptian construction methods to production
Lean docstrings.

## 11. Dependency direction

Silver bridge may import:

~~~text
DkMath.NumberGeometry.Radical
DkMath.SilverRatio.SilverRatioCircle
~~~

Egyptian example may import:

~~~text
DkMath.NumberGeometry.Radical
DkMath.SilverRatio.Sqrt2Lemmas
~~~

The generic NumberGeometry core must remain free of SilverRatio dependencies.

Do not import:

~~~text
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
DkMath.NumberTheory.*
DkMath.FLT.*
~~~

in this checkpoint.

## 12. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/CalibrationAxiomAudit.lean
~~~

or split Silver/Egyptian audits if that fits repository style.

Check the new public declarations and print axioms for substantive theorems.

Expected transitive logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 13. Validation

Run focused builds for every new module and then:

~~~text
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.CalibrationAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for prohibited proof shortcuts.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-006.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. Pair-to-Euclidean conversion chosen.
4. Exact squared-distance bridge theorem.
5. SilverRatio common MassLevelSet theorem.
6. Whether the exact common Silver mass was calculated.
7. Egyptian mass-3 calibration.
8. Radius-3 / mass-9 calibration.
9. Whether Keystone N mass-9 was formalized.
10. Which results reuse NGEO-005 radical landing.
11. Explicit theorem-status table using LEAN-CONFIRMED / EXACT-CALIBRATION /
    RESEARCH-OBSERVATION / DEFERRED.
12. Claims intentionally not made.
13. Build / axiom / diff-check results.
14. Exact proposed scope for NGEO-007.

Stop after NGEO-006.

Do not implement gauge-transition composition from NGEO-007 in the same
checkpoint.
