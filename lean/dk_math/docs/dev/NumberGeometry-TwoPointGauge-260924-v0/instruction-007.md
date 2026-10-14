# NGEO-007 — Gauge transitions and multiplicative composition

You are implementing checkpoint NGEO-007 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-002.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-003.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-006.md

lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/Transport.lean
lean/dk_math/DkMath/NumberGeometry/LevelSet.lean
~~~

NGEO-002 established a relative square-mass gauge and natural counting shells.
NGEO-003 established similarity scaling and shell invariance.
NGEO-006 calibrated concrete Silver/Egyptian examples.

NGEO-007 now formalizes relations between the gauges of two kernels.

## Objective

Introduce a denominator-free multiplicative transition relation:

~~~text
MassScalesBy u K1 K2
  :<-> massGauge K2 = u * massGauge K1.
~~~

This is the generic continuous gauge relation.  The scale factor is a real
number in the core API.

For active source and target kernels, positivity of the scale factor should be
a theorem, not a field stored in the definition.

The key laws are:

~~~text
identity:       1
composition:    u then v  -> u*v
inverse:        u^-1      when u != 0
uniqueness:     active source fixes the scale factor uniquely
~~~

A second central goal is to connect counting inside one kernel to a new gauge:

~~~text
P on natural shell n of K
  -> the kernel from K.source to P has gauge n times the gauge of K.
~~~

This is the exact formal version of the research idea:

~~~text
a counted distance from one two-point geometry can become
the base gauge of a second two-point geometry.
~~~

Do not introduce primality yet.  Prime scale is NGEO-008.

Do not import Units, UnitCycle, DHNT, cyclotomic theory, or FLT.

## Production file

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/GaugeTransition.lean
~~~

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to import/export it.

Do not change earlier core files unless a genuinely missing primitive lemma is
required.

## 1. MassScalesBy

Define:

~~~lean
def MassScalesBy
    (u : ℝ) (K1 K2 : TwoPointKernel) : Prop :=
  massGauge K2 = u * massGauge K1
~~~

Keep this denominator-free.

Do not define the transition initially as a quotient equality.

The relation must be meaningful for degenerate kernels as well as active ones.

## 2. Basic laws

Prove a compact theorem family.

Required:

~~~lean
theorem massScalesBy_refl (K : TwoPointKernel) :
  MassScalesBy 1 K K
~~~

and multiplicative composition:

~~~lean
theorem MassScalesBy.trans
    (h12 : MassScalesBy u K1 K2)
    (h23 : MassScalesBy v K2 K3) :
    MassScalesBy (u * v) K1 K3
~~~

The factor order may be chosen consistently with the final proof, but the
public theorem should document the convention.

Since real multiplication is commutative, do not duplicate both factor orders.

Also prove a direct unfolding theorem if useful:

~~~lean
massScalesBy_iff
~~~

but avoid aliases with no downstream value.

## 3. Factor uniqueness for an active source

An active source has nonzero mass gauge, so the multiplicative factor is
unique.

Prove:

~~~lean
theorem MassScalesBy.factor_unique
    (hK1 : K1.Active)
    (hu : MassScalesBy u K1 K2)
    (hv : MassScalesBy v K1 K2) :
    u = v
~~~

or a namespace-equivalent name.

This theorem will be important in NGEO-008 when a prime integer factor is
attached to a transition.

Do not assert uniqueness when the source gauge is zero.

## 4. Positivity / nonzero factor for active kernels

If both kernels are active and:

~~~text
massGauge K2 = u * massGauge K1,
~~~

then u is positive.

Prove:

~~~lean
theorem MassScalesBy.factor_pos
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active)
    (h2 : K2.Active) :
    0 < u
~~~

and, if useful, the immediate corollary:

~~~lean
theorem MassScalesBy.factor_ne_zero ... :
  u ≠ 0
~~~

Use massGauge positivity; do not use coordinate arguments.

## 5. Inverse transition

For nonzero u, reverse a transition:

~~~lean
theorem MassScalesBy.inv
    (h : MassScalesBy u K1 K2)
    (hu : u ≠ 0) :
    MassScalesBy u⁻¹ K2 K1
~~~

If the cleanest theorem uses active K1/K2 instead of an explicit hu, provide
one primary theorem and a thin active-kernel corollary only if useful.

Do not create a group structure on kernels.

This is a relation-level inverse law.

## 6. Gauge ratio as a secondary quotient view

As with normalizedMass, the denominator-free relation is primary.

A secondary quotient is useful:

~~~lean
def massGaugeRatio (K1 K2 : TwoPointKernel) : ℝ :=
  massGauge K2 / massGauge K1
~~~

Arithmetic interpretation requires active K1.

Required bridge:

~~~lean
theorem massGaugeRatio_eq_of_massScalesBy
    (h1 : K1.Active)
    (h : MassScalesBy u K1 K2) :
    massGaugeRatio K1 K2 = u
~~~

and, if equally clean, the converse:

~~~lean
theorem massScalesBy_of_massGaugeRatio_eq
    (h1 : K1.Active)
    (h : massGaugeRatio K1 K2 = u) :
    MassScalesBy u K1 K2
~~~

If both are clean, package an iff theorem.

Do not make massGaugeRatio the primitive definition.

## 7. Ratio composition

For active K1 and K2, prove:

~~~lean
theorem massGaugeRatio_trans
    (h1 : K1.Active)
    (h2 : K2.Active) :
    massGaugeRatio K1 K3 =
      massGaugeRatio K1 K2 * massGaugeRatio K2 K3
~~~

Check the factor order against the chosen ratio definition.

This theorem is the positive-real multiplicative geometry that will later
connect to Units / logarithmic coordinates.

Do not import those downstream modules yet.

## 8. Distance-square reading

Connect the transition relation to ordinary squared distances.

Required theorem:

~~~lean
theorem massScalesBy_iff_dist_sq
    (u : ℝ) (K1 K2 : TwoPointKernel) :
    MassScalesBy u K1 K2 ↔
      dist K2.source K2.target ^ 2 =
        u * dist K1.source K1.target ^ 2
~~~

Use the existing pairMass_eq_dist_sq theorem.

Do not force an unsquared distance ratio theorem involving sqrt(u) in this
checkpoint.

## 9. Similarity produces a gauge transition

NGEO-003 already proves:

~~~text
massGauge (K.map (similarityMap t c R))
  = c^2 * massGauge K.
~~~

Package this in the new relation:

~~~lean
theorem massScalesBy_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) :
    MassScalesBy (c ^ 2) K
      (K.map (similarityMap t c R))
~~~

This theorem is valid at c = 0.

Also prove, if small, that applying the same similarity to both sides preserves
a scale factor:

~~~lean
theorem MassScalesBy.similarity
    (h : MassScalesBy u K1 K2) :
    MassScalesBy u
      (K1.map (similarityMap t c R))
      (K2.map (similarityMap t c R))
~~~

This should remain true even at c = 0 because both mass gauges are scaled by
the same square factor.

Do not require injectivity for this denominator-free theorem.

## 10. Promote a counted shell to a new gauge

This is a major semantic target of NGEO-007.

Introduce one minimal way to replace the target of a kernel while keeping its
source.

Suggested definition:

~~~lean
def TwoPointKernel.retarget
    (K : TwoPointKernel) (P : Point) : TwoPointKernel where
  source := K.source
  target := P
~~~

Name may differ if repository conventions suggest a better one, but avoid
multiple synonyms.

Prove:

~~~lean
theorem massGauge_retarget
    (K : TwoPointKernel) (P : Point) :
    massGauge (K.retarget P) = pairMass K.source P
~~~

Then the key theorem:

~~~lean
theorem massScalesBy_retarget_of_onNatShell
    (K : TwoPointKernel) {n : ℕ} {P : Point}
    (hP : OnNatShell K n P) :
    MassScalesBy (n : ℝ) K (K.retarget P)
~~~

This theorem should require no activity hypothesis.

It is the formal statement that shell n supplies a new base pair with mass
gauge n times the old one.

Important: this does NOT say the new kernel must remain at the same absolute
location in applications.  NGEO-003 similarity transport can later move,
rotate, reflect, or rescale the resulting kernel.

Do not claim uniqueness of the point P on shell n.

## 11. Optional natural-scale notation wrapper

Do not define a second transition relation specialized to Nat unless it adds
clear value.

The cast:

~~~text
(n : ℝ)
~~~

inside MassScalesBy is sufficient for v0.

NGEO-008 may define a prime-specific predicate using Nat.Prime.

## 12. Level-set parameter scaling

A small scalar theorem is useful:

~~~text
if MassScalesBy u K1 K2,
then the natural-shell n level parameter of K2
is u times the natural-shell n level parameter of K1.
~~~

For example:

~~~lean
theorem natShell_massLevel_scale
    (h : MassScalesBy u K1 K2) (n : ℕ) :
    (n : ℝ) * massGauge K2 =
      u * ((n : ℝ) * massGauge K1)
~~~

This is optional if it is only a one-line ring rewrite and has no immediate
consumer.

Do not invent a point map between arbitrary K1 and K2 from MassScalesBy alone.

A scalar gauge relation does not determine geometric incidence transport.

## 13. False claims to avoid

Do not claim:

- MassScalesBy alone gives a canonical map between points of K1 and K2;
- a scale factor is positive without activity hypotheses;
- the transition factor is unique from a degenerate source;
- every scale factor is a natural number;
- every natural scale is prime or irreducible;
- gauge transition composition is yet a UnitCycle theorem;
- logarithms are part of the core relation.

NGEO-007 is the generic multiplicative gauge layer only.

## 14. Dependency constraints

GaugeTransition.lean should import only:

~~~text
DkMath.NumberGeometry.LevelSet
~~~

or Transport/Gauge directly if LevelSet is unnecessary.

Do not import:

~~~text
DkMath.SilverRatio.*
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
DkMath.NumberTheory.*
DkMath.FLT.*
~~~

The concrete calibration modules from NGEO-006 are consumers, not
dependencies of the generic transition core.

## 15. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/GaugeTransitionAxiomAudit.lean
~~~

Check the new public API and print axioms for substantive theorems.

Expected transitive infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 16. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.GaugeTransition
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.GaugeTransitionAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for prohibited shortcuts and malformed docstrings.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-007.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. Final MassScalesBy definition.
4. Identity/composition/inverse theorem names.
5. Factor uniqueness theorem and required activity hypothesis.
6. Factor positivity theorem and hypotheses.
7. massGaugeRatio API and quotient bridge.
8. Ratio composition theorem.
9. Distance-square interpretation.
10. Similarity-to-transition theorem.
11. Same-similarity preservation theorem, if implemented.
12. retarget API and shell-to-new-gauge theorem.
13. Any level-parameter scaling theorem.
14. Claims intentionally not made.
15. Build / axiom / diff-check results.
16. Exact proposed scope for NGEO-008.

Stop after NGEO-007.

Do not implement prime-scale irreducibility or prime-scale chains from
NGEO-008 in the same checkpoint.
