# NGEO-003 — Similarity transport and shell invariance

You are implementing checkpoint NGEO-003 on branch:

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
lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
~~~

## Objective

Formalize the statement that the two-point gauge geometry is independent of
absolute position, orientation, reflection, and scale.

The core transform is the affine similarity

~~~text
T(P) = t + c • R(P)
~~~

where:

- t : Point is a translation;
- c : ℝ is a real scale;
- R : Point ≃ₗᵢ[ℝ] Point is a real linear isometry equivalence.

The central square-mass law is:

~~~text
pairMass (T A) (T B) = c^2 * pairMass A B.
~~~

From this, natural shell indices must be invariant:

~~~text
OnNatShell K n P
  -> OnNatShell (mapKernel T K) n (T P).
~~~

For active kernels and nonzero scale, normalized mass must also be invariant.

Do not introduce prime scale, radical landing, UnitCycle, logarithmic gauge,
2p phases, or FLT.

## Production file

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/Transport.lean
~~~

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to import/export the new transport module.

Do not modify Basic.lean or Gauge.lean unless a genuinely missing primitive
lemma is discovered. Any such change must be reported explicitly.

## 1. Similarity map representation

Do not create a large custom hierarchy.

Prefer one of these minimal options after checking Mathlib API ergonomics:

### Preferred lightweight definition

~~~lean
def similarityMap
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (P : Point) : Point :=
  t + c • R P
~~~

or an equivalent local abbreviation.

A structure containing t, c, R is acceptable only if it significantly improves
the theorem surface. If a structure is introduced, keep it thin and do not
reimplement Mathlib isometry/similarity machinery.

The primary v0 theorem family should remain directly usable with explicit
parameters.

## 2. Gap transport

First prove the exact vector identity:

~~~lean
theorem pairVec_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A B : Point) :
    pairVec (similarityMap t c R A) (similarityMap t c R B)
      = c • R (pairVec A B)
~~~

The proof should use additive cancellation and linearity, not coordinate
expansion.

This is the foundational transport theorem.

## 3. Pair-mass transport

Prove:

~~~lean
theorem pairMass_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (A B : Point) :
    pairMass (similarityMap t c R A) (similarityMap t c R B)
      = c ^ 2 * pairMass A B
~~~

Use:

- pairVec_similarity;
- norm_smul;
- norm preservation by LinearIsometryEquiv;
- Real.norm_eq_abs if needed;
- sq_abs / abs_sq or an equivalent ring-normal form.

The theorem must work for c = 0 as a square-mass scaling statement.

Do not require c ≠ 0 here.

## 4. Translation / orthogonal / scaling corollaries

Expose small corollaries only if they are genuinely useful.

Suggested:

~~~text
pairMass_translation
pairMass_linearIsometry
pairMass_scale
~~~

Possible forms:

~~~lean
pairMass (t + A) (t + B) = pairMass A B

pairMass (R A) (R B) = pairMass A B

pairMass (c • A) (c • B) = c^2 * pairMass A B
~~~

Do not duplicate the main theorem with many equivalent spelling variants.

Reflection requires no separate custom theorem: any reflection represented by a
LinearIsometryEquiv is covered by pairMass_linearIsometry.

## 5. Kernel transport

Introduce a thin kernel mapper.

Preferred:

~~~lean
def TwoPointKernel.map
    (T : Point → Point)
    (K : TwoPointKernel) : TwoPointKernel where
  source := T K.source
  target := T K.target
~~~

If a more specific name avoids collision with existing map conventions, use it
and record the choice.

Prove simple simp lemmas for source/target if useful.

For the explicit similarity map, connect gauge transport:

~~~lean
theorem massGauge_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) :
    massGauge (K.map (similarityMap t c R))
      = c^2 * massGauge K
~~~

Adjust argument order to match the final map definition.

## 6. Active-kernel transport

For c ≠ 0, similarity transport is injective and therefore preserves activity.

Prove:

~~~lean
theorem active_map_similarity_iff
    (hc : c ≠ 0) :
    (K.map (similarityMap t c R)).Active ↔ K.Active
~~~

or the two useful directions if the iff proof becomes awkward.

Do not assert preservation of Active when c = 0.

The zero-scale map collapses all points and is intentionally excluded from
activity-preservation theorems.

## 7. Natural-shell transport

This is the primary semantic result of NGEO-003.

Prove the denominator-free transport theorem without assuming c ≠ 0:

~~~lean
theorem onNatShell_similarity
    (hP : OnNatShell K n P) :
    OnNatShell
      (K.map (similarityMap t c R))
      n
      (similarityMap t c R P)
~~~

Reason:

~~~text
pairMass(source', point') = c^2 * pairMass(source, point)
massGauge(kernel')        = c^2 * massGauge(kernel)
~~~

and both sides scale by the same factor.

This should work even for c = 0 because OnNatShell is denominator-free.

This theorem is the formal content of:

~~~text
moving, rotating, reflecting, or scaling the entire configuration
does not change its natural shell index.
~~~

## 8. Normalized-mass invariance

For normalized mass, require nonzero scale so the mapped kernel remains active.

Target theorem:

~~~lean
theorem normalizedMass_similarity
    (hK : K.Active)
    (hc : c ≠ 0) :
    normalizedMass
      (K.map (similarityMap t c R))
      (similarityMap t c R P)
      = normalizedMass K P
~~~

There are two acceptable proof routes:

### Route A — direct quotient cancellation

Use pairMass_similarity, massGauge_similarity, and c^2 ≠ 0.

### Route B — shell-only specialization

Not sufficient as the only theorem, because normalizedMass is defined for
general P, not just natural shell points.

Therefore the final theorem should be a general pointwise equality under
active/nonzero hypotheses.

## 9. Distance transport

Since pairMass already equals squared distance, a squared-distance corollary is
useful:

~~~lean
theorem dist_sq_similarity ... :
  dist (T A) (T B)^2 = c^2 * dist A B^2
~~~

Do not force an unsquared distance theorem involving abs c unless it is
essentially free.

If added, the mathematically correct unsquared form is:

~~~text
dist (T A) (T B) = |c| * dist A B.
~~~

Never state c * dist without an assumption 0 ≤ c.

## 10. Shared-point work is deferred

NGEO-004 will own:

- MassLevelSet;
- shared-point predicates;
- image/intersection transport.

NGEO-003 should provide exactly the similarity transport lemmas that NGEO-004
will consume, but should not implement set-level shared-point theory yet.

## 11. Dependency constraints

Transport.lean should import only:

~~~text
DkMath.NumberGeometry.Gauge
~~~

plus narrow Mathlib imports if required.

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

No coordinate expansion in the generic core unless Mathlib forces a tiny local
lemma.

## 12. API discipline

Production names should describe standard mathematics.

Preferred vocabulary:

~~~text
similarityMap
pairVec_similarity
pairMass_similarity
massGauge_similarity
onNatShell_similarity
normalizedMass_similarity
~~~

Avoid metaphorical names in production APIs.

Do not call the map an isometry when |c| ≠ 1.

## 13. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/TransportAxiomAudit.lean
~~~

Check all public declarations and print axioms for substantive transport
theorems.

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 14. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.Transport
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.TransportAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new production files for prohibited proof shortcuts.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-003.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact production files added/changed.
3. Final similarity representation.
4. Exact pairVec transport theorem.
5. Exact pairMass scaling theorem.
6. Translation / isometry / scale corollaries actually exposed.
7. Kernel mapping API.
8. Active preservation theorem and its c ≠ 0 hypothesis.
9. OnNatShell similarity theorem.
10. NormalizedMass invariance theorem.
11. Any distance transport theorem.
12. Build / axiom / diff-check results.
13. Exact proposed scope for NGEO-004.

Stop after NGEO-003.

Do not implement shared-point / level-set theory from NGEO-004 in the same
checkpoint.
