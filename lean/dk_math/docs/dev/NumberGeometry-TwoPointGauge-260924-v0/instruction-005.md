# NGEO-005 — Radical square-mass decomposition and orthogonal landing

You are implementing checkpoint NGEO-005 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-000.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-004.md
lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/Transport.lean
lean/dk_math/DkMath/NumberGeometry/LevelSet.lean
~~~

For later calibration only, inspect but do not import into the generic core unless a
thin example file is explicitly justified:

~~~text
DkMath/SilverRatio/Sqrt2Lemmas.lean
DkMath/SilverRatio/SilverRatioCircle.lean
~~~

NGEO-004 established point-centered mass levels and shared-point transport.
NGEO-005 now isolates the algebraic mechanism by which radical coordinates can
have base-field square mass.

## Objective

Formalize the identity

~~~text
||u + sqrt(m) • v||^2
  = ||u||^2
  + m * ||v||^2
  + 2 * sqrt(m) * <u,v>
~~~

under 0 <= m, and derive the orthogonal landing theorem

~~~text
<u,v> = 0
  ->
||u + sqrt(m) • v||^2
  = ||u||^2 + m * ||v||^2.
~~~

Then connect this vector identity to the existing two-point square mass:

~~~text
pairMass A (A + u + sqrt(m) • v).
~~~

The key semantic point is:

~~~text
radical coordinates do not imply radical square mass;
the radical cross term disappears under orthogonality.
~~~

This is an algebraic landing theorem only. It does not claim that all shared
points are orthogonal or that every geometric construction lands in integers.

## Production file

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/Radical.lean
~~~

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to import/export the new module.

Do not modify Basic/Gauge/Transport/LevelSet unless a genuinely missing
primitive lemma is required.

## 1. Generic decomposition

Prefer a theorem over the existing Point inner-product structure rather than a
coordinate expansion.

Target shape:

~~~lean
theorem norm_sq_add_sqrt_smul
    (u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    ‖u + Real.sqrt m • v‖ ^ 2 =
      ‖u‖ ^ 2
        + m * ‖v‖ ^ 2
        + 2 * Real.sqrt m * ⟪u, v⟫_ℝ
~~~

Equivalent association/order of the right-hand side is acceptable if it gives
a cleaner stable theorem.

Inspect Mathlib for the shortest robust expansion route. Prefer inner-product
identities and Real.sq_sqrt over coordinate expansion into Fin 2.

Do not unfold EuclideanSpace coordinates in the generic theorem.

## 2. Orthogonal landing

Prove the specialization:

~~~lean
theorem norm_sq_add_sqrt_smul_of_inner_eq_zero
    (u v : Point) {m : ℝ} (hm : 0 ≤ m)
    (huv : ⟪u, v⟫_ℝ = 0) :
    ‖u + Real.sqrt m • v‖ ^ 2 =
      ‖u‖ ^ 2 + m * ‖v‖ ^ 2
~~~

If Mathlib has a clean standard orthogonality predicate whose use makes the API
better, a wrapper theorem may be added. The primary theorem may remain in
inner = 0 form if that is simpler and more transparent.

Do not create a custom orthogonality predicate.

## 3. Two-point pair-mass form

Connect the generic decomposition to NumberGeometry.

Preferred theorem:

~~~lean
theorem pairMass_radical
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    pairMass A (A + u + Real.sqrt m • v) =
      ‖u‖ ^ 2
        + m * ‖v‖ ^ 2
        + 2 * Real.sqrt m * ⟪u, v⟫_ℝ
~~~

and the landing corollary:

~~~lean
theorem pairMass_radical_of_inner_eq_zero
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m)
    (huv : ⟪u, v⟫_ℝ = 0) :
    pairMass A (A + u + Real.sqrt m • v) =
      ‖u‖ ^ 2 + m * ‖v‖ ^ 2
~~~

The exact point expression may be parenthesized differently if needed, but the
semantic meaning must remain:

~~~text
center A + base component u + radical component sqrt(m) * v.
~~~

Use pairVec / pairMass and additive cancellation rather than re-proving the norm
identity from scratch.

## 4. Radical sign-conjugation identity

A strongly recommended theorem, if technically small, is the mass difference
between the +sqrt(m) and -sqrt(m) conjugate points.

Let:

~~~text
P+ = A + u + sqrt(m) • v
P- = A + u - sqrt(m) • v.
~~~

Target:

~~~lean
theorem pairMass_radical_conj_sub
    (A u v : Point) {m : ℝ} (hm : 0 ≤ m) :
    pairMass A (A + u + Real.sqrt m • v)
      - pairMass A (A + u - Real.sqrt m • v)
      =
    4 * Real.sqrt m * ⟪u, v⟫_ℝ
~~~

Equivalent sign/order is acceptable if documented.

This theorem makes the C2 radical conjugation visible:

~~~text
sqrt(m) <-> -sqrt(m)
~~~

and isolates the odd cross term.

## 5. Equal-conjugate-mass criterion

If section 4 remains small, prove the key criterion for positive m:

~~~lean
theorem pairMass_radical_conj_eq_iff_inner_eq_zero
    (A u v : Point) {m : ℝ} (hm : 0 < m) :
    pairMass A (A + u + Real.sqrt m • v)
      =
    pairMass A (A + u - Real.sqrt m • v)
      ↔
    ⟪u, v⟫_ℝ = 0
~~~

Use Real.sqrt_pos.2 hm to justify cancellation.

This is an important bridge for later shared/incidence geometry:

~~~text
equality under radical conjugation
    <-> orthogonality
    -> radical cross-term cancellation
    -> square-mass landing.
~~~

Do not overstate this as a theorem about arbitrary SharedPoint configurations.
It concerns this explicit conjugate pair only.

If the iff theorem requires disproportionate proof infrastructure, record it as
deferred and keep the decomposition + orthogonal landing core.

## 6. A neutral landing theorem

The term landing should mean only that the radical cross term has disappeared.

Do not introduce an integer-valued predicate yet.

A theorem such as pairMass_radical_of_inner_eq_zero may itself be the public
landing theorem. Avoid duplicate aliases unless the semantic name materially
improves the API.

## 7. Minimal sqrt(2) calibration

The generic production file must not depend on SilverRatio.

However, this checkpoint should verify at least one concrete calibration,
preferably in a test/example file.

Use the existing checked theorem:

~~~text
DkMath.SilverRatio.Sqrt2.sqrt2_sq :
  sqrt2 ^ 2 = 2
~~~

A suitable calibration is the vector analogue of:

~~~text
(-1)^2 + (sqrt 2)^2 = 3.
~~~

For example choose orthogonal coordinate directions u,v in
EuclideanSpace ℝ (Fin 2) with unit norms and show the generic theorem reduces
to square mass 3 for a point equivalent to (-1, sqrt 2) or (1, sqrt 2).

The exact coordinates are not important; the calibration should demonstrate:

~~~text
1 + 2 = 3
~~~

through the generic radical-landing theorem.

If constructing concrete EuclideanSpace coordinates is noisy, put the
calibration in DkMathTest/NumberGeometry rather than production and explain the
representation cost in the report.

Do not refactor SilverRatio.Circle in NGEO-005.

## 8. Optional natural-m parameter wrapper

The core theorem over m : ℝ is preferred because the geometry is real.

If later counting work benefits from a thin wrapper using m : Nat and
sqrt((m : ℝ)), it may be added only if trivial.

Do not specialize the whole API to natural m.

## 9. Interaction with MassLevelSet

A small corollary is acceptable if it directly improves the later bridge:

~~~text
orthogonal radical point
  lies in MassLevelSet A (||u||^2 + m*||v||^2).
~~~

Possible theorem:

~~~lean
theorem mem_massLevelSet_radical_of_inner_eq_zero ...
~~~

This is optional.

Do not attempt to infer orthogonality from arbitrary two-circle intersection in
this checkpoint.

## 10. False claims to avoid

Do not claim:

- every SharedPoint forces orthogonality;
- every radical point has rational or integer mass;
- every mass landing is a natural shell;
- sqrt(m) is irrational;
- the theorem classifies SilverRatio or Egyptian constructions;
- coordinate irrationality implies non-integrality of a number field element;
- any FLT consequence.

The theorem is exactly a square-mass decomposition and its orthogonal
cancellation consequence.

## 11. Dependency constraints

Radical.lean should import only:

~~~text
DkMath.NumberGeometry.LevelSet
~~~

plus narrow Mathlib inner-product/sqrt material if required.

The generic production file must not import:

~~~text
DkMath.SilverRatio.*
DkMath.CosmicFormula.*
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
DkMath.NumberTheory.*
DkMath.FLT.*
~~~

A test/calibration file may import DkMath.SilverRatio.Sqrt2Lemmas.

## 12. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/RadicalAxiomAudit.lean
~~~

Check all public declarations and print axioms for substantive theorems.

If a sqrt(2) calibration is placed in a separate test file, include it in the
same audit file if practical.

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 13. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.Radical
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.RadicalAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for prohibited proof shortcuts.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-005.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact production/test files added or changed.
3. Final generic radical decomposition theorem.
4. Final orthogonal landing theorem.
5. Pair-mass specialization.
6. Whether radical sign-conjugation difference was proved.
7. Whether equal conjugate mass iff orthogonality was proved.
8. Any MassLevelSet corollary.
9. Concrete sqrt(2) calibration result.
10. Exact use of existing SilverRatio sqrt2 lemmas, if any.
11. Explicit list of claims intentionally not made.
12. Build / axiom / diff-check results.
13. Exact proposed scope for NGEO-006.

Stop after NGEO-005.

Do not implement the Silver/Egyptian construction bridge from NGEO-006 in the
same checkpoint.
