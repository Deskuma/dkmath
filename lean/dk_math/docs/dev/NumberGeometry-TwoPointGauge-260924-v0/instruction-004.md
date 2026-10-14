# NGEO-004 — Mass level sets and shared-point transport

You are implementing checkpoint NGEO-004 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-000.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-001.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-002.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-003.md
lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/Transport.lean
~~~

NGEO-003 has established the core similarity law:

~~~text
pairMass (T A) (T B) = c^2 * pairMass A B
~~~

for

~~~text
T(P) = t + c • R(P),
~~~

together with shell and normalized-mass transport.

## Objective

Introduce point-centered square-mass level sets and formalize the statement
that shared/intersection points are transported naturally by the similarity
map.

The conceptual layer is:

~~~text
MassLevelSet A rho
    := { P | pairMass A P = rho }

P shared by two level sets
    := P belongs to both sets

similarity transport
    -> both level conditions scale by c^2
    -> the same point relation is preserved
~~~

This checkpoint should make precise the earlier geometric claim that the
shared point does not "drift" when the entire construction is translated,
rotated, reflected, or rescaled.

Do not introduce SilverRatio-specific coordinates yet; that is a later bridge.

Do not implement radical landing, prime scale, UnitCycle, logarithms, 2p
phases, cyclotomic theory, or FLT.

## Production file

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/LevelSet.lean
~~~

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to import/export the new module.

Do not modify Basic/Gauge/Transport unless a genuinely missing primitive lemma
is required. Any such change must be justified in report-004.md.

## 1. MassLevelSet

Define the point-centered square-mass level set:

~~~lean
def MassLevelSet (A : Point) (rho : ℝ) : Set Point :=
  {P | pairMass A P = rho}
~~~

The parameter is square mass, not radius.

Do not call rho a radius in production docstrings.

The geometric reading as a circle for rho > 0 is interpretation only.

Required basic theorem:

~~~lean
@[simp] theorem mem_massLevelSet
    (A P : Point) (rho : ℝ) :
    P ∈ MassLevelSet A rho ↔ pairMass A P = rho
~~~

If definition unfolding makes this theorem rfl, expose it only if it improves
downstream readability.

## 2. Zero level

Prove that the zero-mass level set is exactly the singleton center.

Preferred set equality:

~~~lean
@[simp] theorem massLevelSet_zero (A : Point) :
  MassLevelSet A 0 = {A}
~~~

Use pairMass_eq_zero_iff.

Optionally prove negative levels are empty if this is one line from
pairMass_nonneg:

~~~lean
theorem massLevelSet_eq_empty_of_neg
    {A : Point} {rho : ℝ} (hrho : rho < 0) :
    MassLevelSet A rho = ∅
~~~

This is useful but not required if it distracts from the transport layer.

Do not prove global nonemptiness for every rho >= 0 in this checkpoint unless
it is essentially free.

## 3. Bridge to natural counting shells

Connect NGEO-002 directly to the new level-set language.

Required theorem:

~~~lean
theorem onNatShell_iff_mem_massLevelSet
    (K : TwoPointKernel) (n : ℕ) (P : Point) :
    OnNatShell K n P ↔
      P ∈ MassLevelSet K.source ((n : ℝ) * massGauge K)
~~~

This theorem should be definitional or nearly so.

This gives the intended interpretation:

~~~text
natural shell n
=
mass level n * base mass gauge.
~~~

Do not introduce another shell definition.

## 4. Forward level-set transport — valid even at c = 0

Using pairMass_similarity, prove pointwise transport:

~~~lean
theorem mem_massLevelSet_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    {A P : Point} {rho : ℝ}
    (hP : P ∈ MassLevelSet A rho) :
    similarityMap t c R P ∈
      MassLevelSet
        (similarityMap t c R A)
        (c ^ 2 * rho)
~~~

This theorem must hold for every real c, including c = 0.

Also expose the corresponding set-image inclusion if useful:

~~~lean
theorem image_massLevelSet_similarity_subset
    ... :
    similarityMap t c R '' MassLevelSet A rho
      ⊆ MassLevelSet (similarityMap t c R A) (c ^ 2 * rho)
~~~

The forward inclusion is valid at zero scale.

## 5. Important zero-scale boundary

Do not claim unconditional set equality:

~~~text
T '' MassLevelSet A rho
  = MassLevelSet (T A) (c^2 * rho)
~~~

for c = 0.

At c = 0 the target level is the zero level set, hence a singleton, while the
source level may be empty (for example rho < 0), so image equality is not
automatic.

Any reverse transport / set equality theorem must require c ≠ 0, or otherwise
supply explicit source nonemptiness conditions.

This boundary must be recorded in report-004.md.

## 6. Similarity injectivity for nonzero scale

NGEO-003 proved activity preservation, but NGEO-004 set transport benefits from
an explicit injectivity theorem.

If not already available from Mathlib in a convenient form, prove:

~~~lean
theorem similarityMap_injective
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (hc : c ≠ 0) :
    Function.Injective (similarityMap t c R)
~~~

A short proof may use:

- linear isometry injectivity;
- smul_left_cancel0 / scalar nonzero cancellation;
- or pairMass_similarity plus pairMass_eq_zero_iff.

Prefer the shortest robust proof.

If Mathlib already supplies the needed injectivity through a composed
equivalence, reuse it rather than reproving.

## 7. Reverse / exact level-set transport under c ≠ 0

Investigate the cleanest theorem surface.

Preferred target if technically small:

~~~lean
theorem image_massLevelSet_similarity
    (hc : c ≠ 0) :
    similarityMap t c R '' MassLevelSet A rho
      =
    MassLevelSet
      (similarityMap t c R A)
      (c ^ 2 * rho)
~~~

To prove equality, you will need surjectivity onto the ambient Point as well as
the scaled level relation.

Options:

1. construct a thin inverse similarity explicitly;
2. package nonzero-scale similarityMap as an Equiv;
3. use existing Mathlib affine equivalence / dilation machinery if cheaper.

Do not create a large custom similarity hierarchy just to prove this theorem.

If exact set equality would require disproportionate infrastructure, Outcome A
may still stop with:

- forward image inclusion for arbitrary c;
- pointwise iff transport under c ≠ 0, using an explicit inverse lemma.

Record the exact strongest clean theorem obtained.

Do not force a heavy abstraction.

## 8. SharedPoint vocabulary

Introduce a minimal generic shared-point predicate only if it adds readability.

Preferred definition:

~~~lean
def SharedPoint (S U : Set Point) (P : Point) : Prop :=
  P ∈ S ∧ P ∈ U
~~~

Alternative argument order is acceptable if it reads better in theorem use.

Do not add multiple aliases for intersection membership.

Expose:

~~~lean
theorem sharedPoint_iff_mem_inter ... :
  SharedPoint S U P ↔ P ∈ S ∩ U
~~~

if useful.

The key semantic target is not a new set theory; it is a readable theorem that
one point simultaneously satisfies two geometric constraints.

## 9. Shared mass-level transport

Prove the direct geometric theorem:

~~~lean
theorem sharedPoint_massLevelSet_similarity
    (hP :
      SharedPoint
        (MassLevelSet A rho)
        (MassLevelSet B sigma)
        P) :
    SharedPoint
      (MassLevelSet (similarityMap t c R A) (c ^ 2 * rho))
      (MassLevelSet (similarityMap t c R B) (c ^ 2 * sigma))
      (similarityMap t c R P)
~~~

This forward theorem should hold for c = 0.

It is the direct formalization of:

~~~text
if P is a common point of two mass constraints,
then the transported point is a common point of the transported constraints.
~~~

No arithmetic landing claim follows from this theorem by itself.

## 10. Intersection naturality

For c ≠ 0, prove the cleanest available set-level intersection theorem.

Possible target:

~~~lean
theorem image_inter_similarity
    (hc : c ≠ 0)
    (S U : Set Point) :
    similarityMap t c R '' (S ∩ U)
      =
    (similarityMap t c R '' S) ∩
    (similarityMap t c R '' U)
~~~

This is generic set theory from injectivity and should reuse Mathlib if
available.

If exact theorem names differ, inspect Mathlib rather than hand-rolling a long
proof.

Then specialize it to MassLevelSet only if that produces a genuinely useful
public theorem.

Do not duplicate Set.image_inter ownership under many equivalent names.

## 11. Optional circle/sphere bridge

A positive mass level rho corresponds to a metric sphere of radius sqrt(rho).

This is not required for NGEO-004.

If Mathlib makes the theorem very small, a bridge may be added under a
nonnegativity hypothesis, but it must not become the main proof infrastructure.

The NumberGeometry primitive remains MassLevelSet, not Metric.sphere.

It is fully acceptable to defer this to a later example/bridge checkpoint.

## 12. Dependency constraints

LevelSet.lean should import only:

~~~text
DkMath.NumberGeometry.Transport
~~~

plus narrow Mathlib Set imports if required.

Do not import:

~~~text
DkMath.SilverRatio.*
DkMath.CosmicFormula.*
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
DkMath.NumberTheory.*
DkMath.FLT.*
~~~

No coordinate expansion.

## 13. False claims to avoid

Do not claim:

- every two mass level sets intersect;
- a shared point is unique;
- a shared point has integer or radical-integer normalized mass;
- every nonnegative MassLevelSet is inhabited unless proved;
- c = 0 gives exact image equality for arbitrary rho;
- circle geometry itself proves any number-theory statement.

NGEO-004 is transport/incidence infrastructure only.

## 14. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/LevelSetAxiomAudit.lean
~~~

Check the public declarations and print axioms for substantive theorems.

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 15. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.LevelSet
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.LevelSetAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for prohibited proof shortcuts.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-004.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact production files added/changed.
3. Final MassLevelSet definition.
4. Zero-level theorem and any negative-level theorem.
5. OnNatShell-to-level-set bridge.
6. Forward similarity membership/image transport theorem(s).
7. Exact handling of the c = 0 boundary.
8. Any nonzero-scale injectivity / inverse / set-equality theorem.
9. Final SharedPoint API, if introduced.
10. Shared mass-level transport theorem.
11. Intersection naturality theorem.
12. Any intentionally deferred sphere/circle bridge.
13. Build / axiom / diff-check results.
14. Exact proposed scope for NGEO-005.

Stop after NGEO-004.

Do not implement radical decomposition or landing from NGEO-005 in the same
checkpoint.
