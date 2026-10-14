# NGEO-008 — Prime scale steps, irreducibility, and prime-scale chains

You are implementing checkpoint NGEO-008 on branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-007.md

lean/dk_math/DkMath/NumberGeometry/Basic.lean
lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/GaugeTransition.lean
~~~

NGEO-007 established the generic real-valued transition relation:

~~~lean
def MassScalesBy (u : ℝ) (K1 K2 : TwoPointKernel) : Prop :=
  massGauge K2 = u * massGauge K1
~~~

with factor uniqueness from an active source, positivity for active endpoints,
composition, inverse, ratio, similarity transport, and natural-shell promotion.

NGEO-008 adds the first discrete arithmetic landing into that continuous gauge
space.

## Objective

Formalize a prime-labelled gauge step:

~~~text
K1 --p--> K2
~~~

meaning:

~~~text
p is a natural prime
and
massGauge K2 = p * massGauge K1.
~~~

Then prove three core facts:

1. the prime label is intrinsic when the source kernel is active;
2. a prime-labelled scale cannot factor into two non-unit natural scale labels;
3. finite prime-labelled chains multiply their labels.

This is the precise v0 meaning of:

~~~text
prime
=
irreducible natural square-mass multiplier between two active gauge worlds.
~~~

Do not connect to DkMath.Units, UnitCycle, DHNT, logarithms, cyclotomic theory,
or FLT in this checkpoint.

## Naming collision warning

The repository already has the unrelated number-theory predicate:

~~~text
DkMath.NumberTheory.StructuralArithmetic.PrimeScaleGeneratedBy
~~~

Do not import it and do not identify it with this geometry API.

Use the explicit name:

~~~text
PrimeScaleStep
~~~

for NumberGeometry.

## Production files

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/PrimeScale.lean
~~~

If the finite chain implementation is large enough to deserve separation, it
may live in:

~~~text
lean/dk_math/DkMath/NumberGeometry/PrimeScaleChain.lean
~~~

Otherwise keep the bounded v0 chain in PrimeScale.lean.

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to export the new public module(s).

## 1. PrimeScaleStep

Prefer an explicitly labelled predicate:

~~~lean
def PrimeScaleStep
    (p : ℕ) (K1 K2 : TwoPointKernel) : Prop :=
  Nat.Prime p ∧ MassScalesBy (p : ℝ) K1 K2
~~~

The prime p must be an explicit argument, not hidden existentially, because
chain labels and uniqueness matter.

A later convenience wrapper such as:

~~~text
∃ p, PrimeScaleStep p K1 K2
~~~

is optional and should not replace the labelled primitive.

## 2. Basic projections

Expose thin readable accessors/theorems if useful:

~~~text
PrimeScaleStep.prime
PrimeScaleStep.massScalesBy
~~~

Do not introduce a structure merely to get field notation unless it clearly
improves the implementation.

## 3. Prime label uniqueness

For an active source, two prime labels on the same transition must agree.

Target:

~~~lean
theorem PrimeScaleStep.label_unique
    (hK1 : K1.Active)
    (hp : PrimeScaleStep p K1 K2)
    (hq : PrimeScaleStep q K1 K2) :
    p = q
~~~

Use:

~~~text
MassScalesBy.factor_unique
~~~

and exact cast recovery. Do not re-prove gauge cancellation.

This theorem is important: the prime label is not an arbitrary annotation once
the source gauge is nonzero.

## 4. Activity propagation

A prime factor is positive. Therefore an active source remains active after a
PrimeScaleStep.

Target:

~~~lean
theorem PrimeScaleStep.target_active
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    K2.Active
~~~

This should use Nat.Prime positivity and the mass-gauge equation.

A reverse theorem is optional if equally small.

Do not assert activity from a degenerate source.

## 5. Natural shell -> prime scale

This is the direct formalization of the original construction idea.

NGEO-007 already proved:

~~~text
OnNatShell K n P
  -> MassScalesBy n K (K.retarget P).
~~~

Now specialize a prime shell:

~~~lean
theorem primeScaleStep_retarget_of_onNatShell
    (hp : Nat.Prime p)
    (hP : OnNatShell K p P) :
    PrimeScaleStep p K (K.retarget P)
~~~

No activity hypothesis is needed for the relation itself.

Optionally prove the active-target corollary when K.Active.

This theorem means:

~~~text
a distance counted as shell p in one two-point geometry
may be promoted to the base pair of a second geometry,
whose square-mass gauge is p times the first.
~~~

Do not state that the new kernel must remain at the same physical location in
all applications; similarity transport remains available separately.

## 6. Prime irreducibility among natural scale factors

This is the central theorem.

Suppose:

~~~text
K1 --a--> K2 --b--> K3
~~~

where a,b are natural scale labels, and also:

~~~text
K1 --p--> K3
~~~

with p prime.

For an active source K1, prove:

~~~lean
theorem PrimeScaleStep.irreducible
    (hp13 : PrimeScaleStep p K1 K3)
    (h12 : MassScalesBy (a : ℝ) K1 K2)
    (h23 : MassScalesBy (b : ℝ) K2 K3)
    (hK1 : K1.Active) :
    a = 1 ∨ b = 1
~~~

Recommended proof route:

1. compose h12 and h23 with MassScalesBy.trans;
2. use MassScalesBy.factor_unique at active K1;
3. recover the natural equality p = a*b by exact cast reasoning;
4. use Mathlib Nat.Prime multiplication API, preferably Nat.prime_mul_iff or
   another canonical prime divisor theorem.

Do not manually re-prove elementary primality.

No positivity hypotheses on a,b should be added unless Lean genuinely requires
them; primality of p and p = a*b already supplies the relevant arithmetic
restriction.

## 7. Scope of the irreducibility claim

Be precise in docstrings.

The theorem proves:

~~~text
prime-labelled natural scale transition
cannot decompose into two natural-labelled non-unit transitions.
~~~

It does NOT prove:

- irreducibility against arbitrary positive real factors;
- uniqueness of an intermediate geometric kernel;
- algebraic primality in an arbitrary ring;
- a prime-distribution theorem.

The discrete restriction to natural labels is essential.

## 8. Composite-factor converse — optional bounded investigation

It is mathematically possible in R^2 to construct an intermediate kernel with
a prescribed nonnegative natural mass multiplier using similarity scaling by
sqrt(a).

Investigate, but do not force, a theorem of the following form:

~~~text
if n = a*b and MassScalesBy n K1 K3,
then there exists K2 with
  MassScalesBy a K1 K2
and
  MassScalesBy b K2 K3.
~~~

A possible construction is a similarity image of K1 at scale sqrt(a).

Only add this theorem if it stays small and does not require a new similarity
hierarchy.

If implemented, distinguish:

~~~text
prime -> every natural factorization is trivial
~~~

from:

~~~text
composite natural label -> some geometric intermediate can be constructed.
~~~

If deferred, record it explicitly. The prime irreducibility theorem is
required; the converse is not.

## 9. PrimeScaleChain

Introduce a finite chain API that is minimal and induction-friendly.

Preferred representation is an inductive endpoint relation indexed by the list
of prime labels:

~~~lean
inductive PrimeScaleChain :
    TwoPointKernel → TwoPointKernel → List ℕ → Prop
  | nil (K) :
      PrimeScaleChain K K []
  | cons
      (hStep : PrimeScaleStep p K1 K2)
      (hTail : PrimeScaleChain K2 K3 ps) :
      PrimeScaleChain K1 K3 (p :: ps)
~~~

Exact binder order may be adjusted.

This avoids building a separate vector of kernels and keeps intermediate
kernels existential through the constructor history.

Do not overengineer a category or graph structure.

## 10. Chain total scale

Prove by induction:

~~~lean
theorem PrimeScaleChain.massScalesBy_prod
    (h : PrimeScaleChain K1 K2 ps) :
    MassScalesBy ((ps.prod : ℕ) : ℝ) K1 K2
~~~

or the equivalent cast normal form accepted by Lean.

For the empty list, the product is 1 and uses massScalesBy_refl.

For cons, reuse MassScalesBy.trans.

Do not manually multiply gauge equations at every step.

## 11. Chain endpoint activity

If the source is active, every prime step preserves activity, so the endpoint
of a prime chain should be active.

If small, prove:

~~~lean
theorem PrimeScaleChain.target_active
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active) :
    K2.Active
~~~

This theorem is strongly useful for later UnitCycle/log bridges but is not
worth heavy bookkeeping.

## 12. Prime-power calibration

Add one bounded theorem showing repeated same-prime labels produce a prime
power scale.

Preferred chain statement:

~~~lean
theorem PrimeScaleChain.massScalesBy_pow
    (h : PrimeScaleChain K1 K2 (List.replicate k p)) :
    MassScalesBy ((p ^ k : ℕ) : ℝ) K1 K2
~~~

using List.prod_replicate or the current Mathlib equivalent.

If List.replicate/product normalization is unexpectedly noisy, a simpler
two-step calibration is acceptable:

~~~text
PrimeScaleStep p K1 K2
PrimeScaleStep p K2 K3
-> MassScalesBy (p^2) K1 K3.
~~~

Prefer the general replicate theorem if it remains small.

## 13. Distance interpretation

A thin theorem may expose the prime step as:

~~~text
dist(K2.source,K2.target)^2
  = p * dist(K1.source,K1.target)^2.
~~~

This should be a corollary of massScalesBy_iff_dist_sq.

Do not force the unsquared form:

~~~text
r2 = sqrt(p) * r1
~~~

in NGEO-008 if it introduces unnecessary square-root sign work.

The square-mass statement is the production kernel.

## 14. No Units / UnitCycle yet

Although prime chains are multiplicative, do not import or bridge:

~~~text
DkMath.Units.*
DkMath.UnitCycle.*
DkMath.DHNT.*
~~~

Those are NGEO-009.

Likewise do not add logarithms; those are NGEO-010.

## 15. Dependency constraints

PrimeScale.lean should import only:

~~~text
DkMath.NumberGeometry.GaugeTransition
~~~

plus narrow Mathlib Nat.Prime/List material if required.

Do not import DkMath NumberTheory prime infrastructure unless a canonical
Mathlib theorem is genuinely unavailable.

In particular do not import FLT, cyclotomic, PrimitiveSet, or
StructuralArithmetic just to obtain primality facts.

## 16. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/PrimeScaleAxiomAudit.lean
~~~

Check public declarations and print axioms for substantive theorems.

Expected transitive logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 17. Validation

Run focused builds for all new modules, then:

~~~text
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.PrimeScaleAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for forbidden proof shortcuts and malformed docstrings.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-008.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. Final PrimeScaleStep definition.
4. Prime label uniqueness theorem.
5. Activity propagation theorem.
6. Prime-shell retarget theorem.
7. Exact irreducibility theorem and its hypotheses.
8. Whether the composite-factor converse was implemented or deferred.
9. Final PrimeScaleChain representation.
10. Chain product theorem.
11. Chain activity theorem, if implemented.
12. Prime-power calibration theorem.
13. Distance-square interpretation, if exposed.
14. Claims intentionally not made.
15. Build / axiom / diff-check results.
16. Exact proposed scope for NGEO-009.

Stop after NGEO-008.

Do not implement Units / UnitCycle / DHNT bridges from NGEO-009 in the same
checkpoint.
