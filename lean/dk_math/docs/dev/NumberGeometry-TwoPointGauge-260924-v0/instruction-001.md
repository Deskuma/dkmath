# NGEO-001 — TwoPointKernel and PairMass

You are implementing checkpoint NGEO-001 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-000.md
~~~

NGEO-000 froze the v0 representation and ownership boundary.

## Frozen design

Use this v0 point representation:

~~~lean
abbrev Point := EuclideanSpace ℝ (Fin 2)
~~~

Do not use CF2D.Vec ℝ or ℝ × ℝ as the core point type.

Keep these ownership boundaries:

- CF2D keeps Vec.q2, q2_star, UnitKernel, and CF2D LevelSet.
- SilverRatio keeps its local Point := ℝ × ℝ, dist_sq, and concrete circle theorem.
- NumberGeometry owns ordinary two-point Euclidean gap / pair-square-mass semantics.
- No Units, UnitCycle, DHNT, prime, cyclotomic, or FLT dependency belongs in this checkpoint.

## Objective

Implement the minimal production core for two-point geometry over R^2.

The mathematical kernel is:

~~~text
A, B : Point
gap(A,B)      = B - A
pairMass(A,B) = ||B - A||^2
~~~

and the first semantic split is:

~~~text
pairMass A B = 0  <->  A = B
0 < pairMass A B  <->  A != B
~~~

Stop at this core.

Do not implement natural-number shells, normalized quotient gauges,
similarity transport, radical landing, prime scale, logarithms, or 2p phases.

## Required production files

Prefer the thin layout frozen by NGEO-000.

Create at least:

~~~text
lean/dk_math/DkMath/NumberGeometry/Basic.lean
~~~

Add a facade only if useful and minimal:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

Do not create many one-definition files in this checkpoint.

If TwoPointKernel fits cleanly in Basic.lean, keep it there for v0.

## Namespace

Use:

~~~lean
namespace DkMath.NumberGeometry
~~~

No CosmicFormula vocabulary in core declaration names.

## Required definitions

### Point

~~~lean
abbrev Point := EuclideanSpace ℝ (Fin 2)
~~~

### Pair gap

Preferred direction:

~~~lean
def pairVec (A B : Point) : Point := B - A
~~~

The orientation is source-to-target: A -> B is B - A.

### Pair square mass

Preferred definition:

~~~lean
def pairMass (A B : Point) : ℝ := ‖pairVec A B‖ ^ 2
~~~

An equivalent inner-product definition is allowed only if it materially
simplifies proofs or interoperability. If the implementation chooses the
inner-product form, report the reason and provide the norm-square equality.

Do not define ordinary distance again; mathlib dist remains the distance owner.

### TwoPointKernel

Introduce the light data carrier:

~~~lean
structure TwoPointKernel where
  source : Point
  target : Point
~~~

Do not store nondegeneracy in the structure.

The active/separated condition must remain a predicate so degenerate pairs are
representable and zero remains part of the theory.

Preferred predicate:

~~~lean
def TwoPointKernel.Active (K : TwoPointKernel) : Prop :=
  K.source ≠ K.target
~~~

Do not add multiple synonyms without a concrete use.

## Required theorem surface

At minimum prove:

~~~lean
@[simp] theorem pairVec_self (A : Point) :
  pairVec A A = 0

@[simp] theorem pairMass_self (A : Point) :
  pairMass A A = 0

theorem pairMass_nonneg (A B : Point) :
  0 ≤ pairMass A B

@[simp] theorem pairMass_eq_zero_iff (A B : Point) :
  pairMass A B = 0 ↔ A = B

theorem pairMass_pos_iff (A B : Point) :
  0 < pairMass A B ↔ A ≠ B
~~~

Also expose kernel-specialized forms if they are genuinely useful and thin.

Prefer direct statements such as:

~~~lean
pairMass K.source K.target = 0 ↔ K.source = K.target
0 < pairMass K.source K.target ↔ K.Active
~~~

Avoid awkward double-negation APIs.

## Strongly recommended convenience lemmas

Add only if trivial and useful:

~~~text
pairVec_eq_zero_iff
pairMass_comm
pairMass_eq_norm_sq
pairMass_eq_dist_sq
~~~

pairMass_comm is useful because the oriented gap changes sign while the mass
does not.

pairMass_eq_dist_sq should state the exact relation to mathlib distance without
creating a new distance API.

Do not add a broad algebraic lemma collection merely because the proofs are
easy.

## Proof guidance

Use standard mathlib Euclidean/norm facts. Likely ingredients include:

~~~text
sub_eq_zero
norm_nonneg
sq_nonneg
sq_eq_zero_iff
norm_eq_zero
dist_eq_norm
dist_comm
norm_neg
~~~

or the corresponding inner-product lemmas if that route is cleaner.

Prefer short invariant proofs over coordinate expansion.

Do not unfold EuclideanSpace into Fin 2 -> ℝ unless necessary.

The purpose of the chosen representation is to avoid coordinate-level proofs
in the generic core.

## Semantic calibration

The following interpretations must be justified by theorem statements, not new
types:

~~~text
GeoZero:
  A = B
  <-> pairMass A B = 0

Geometric separation:
  A != B
  <-> 0 < pairMass A B
~~~

Do not introduce an inductive GeoZero, GeoSucc, Peano geometry object, or
custom natural-number structure.

## Dependency constraints

Production core may import only mathlib material needed for Euclidean space
and norm/inner-product reasoning.

Do not import:

~~~text
DkMath.CosmicFormula.*
DkMath.SilverRatio.*
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
DkMath.NumberTheory.*
DkMath.FLT.*
~~~

If the facade DkMath.NumberGeometry is added, it should import only the new
NumberGeometry production module(s).

## Documentation constraints

Docstrings should explain:

- pairVec A B is the oriented gap from source A to target B;
- pairMass A B is squared Euclidean distance, interpreted later as two-point square mass;
- TwoPointKernel stores the pair only and permits the degenerate zero case;
- Active means the pair has nonzero separation.

Do not make claims about primes, shared-point arithmetic, radical landing,
UnitCycle, 2p phases, or FLT in production docstrings.

## Validation

Run focused builds:

~~~text
lake build DkMath.NumberGeometry.Basic
lake build DkMath.NumberGeometry
~~~

if the facade exists.

Then run:

~~~text
lake build DkMath
git diff --check
~~~

Run #print axioms on every substantive new theorem, or create a small DkMathTest
audit file if that is the repository-preferred pattern.

No:

~~~text
sorry
admit
sorryAx
declared axiom
unsafe proof shortcut
~~~

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-001.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact production files added/changed.
3. Final public API names.
4. Chosen pairMass representation and why.
5. Proof route for zero/positive separation.
6. Build results.
7. Axiom audit results.
8. git diff --check result.
9. Git diff summary.
10. Exact proposed scope for NGEO-002.

Stop after NGEO-001.

Do not implement NGEO-002 in the same checkpoint.
