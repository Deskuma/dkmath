# NGEO-010 — Logarithmic gauge coordinates

Branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-009.md

lean/dk_math/DkMath/NumberGeometry/Gauge.lean
lean/dk_math/DkMath/NumberGeometry/GaugeTransition.lean
lean/dk_math/DkMath/NumberGeometry/PrimeScale.lean
lean/dk_math/DkMath/NumberGeometry/Bridge/UnitCycle.lean

lean/dk_math/DkMath/DHNT/DHNT_Base.lean
~~~

NGEO-009 established an exact bridge from active square-mass gauges to
DkMath.DHNT.Unit and verified multiplicative gauge composition and no-cycle
behavior.

NGEO-010 adds an optional analytic coordinate in which multiplicative gauge
transitions become additive increments.

## Objective

For an active kernel K, define the logarithmic square-mass coordinate:

~~~text
G(K) = log(massGauge K).
~~~

Then formalize:

~~~text
MassScalesBy u K1 K2
  -> G(K2) - G(K1) = log u
~~~

under active endpoint hypotheses.

Specialize to prime scales:

~~~text
PrimeScaleStep p K1 K2
  -> G(K2) - G(K1) = log p.
~~~

Finally connect square-mass log coordinates to ordinary distance log
coordinates:

~~~text
G(K) = 2 * log(dist(K.source,K.target)).
~~~

Hence a prime square-mass step has distance-log increment:

~~~text
log r2 - log r1 = (1/2) * log p.
~~~

This checkpoint is an analytic bridge only. Do not alter the denominator-free
core definitions from NGEO-001 through NGEO-008.

## Production file

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/Bridge/LogGauge.lean
~~~

Preferred imports:

~~~text
DkMath.NumberGeometry.Bridge.UnitCycle
~~~

plus narrow Mathlib log material only if needed.

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to expose the bridge if consistent with the existing public facade.

Do not import NPUnit, UnitNatLayers, NumberTheory, CosmicFormula, cyclotomic,
or FLT modules.

## 1. Reuse DHNT log ownership

DHNT already owns:

~~~text
DkMath.DHNT.DUnit.logU
~~~

with:

~~~text
logU(u) = Real.log u.val.
~~~

Prefer defining NumberGeometry mass-log coordinate through the exact massUnit
bridge rather than creating an unrelated positive-real wrapper.

Suggested definition:

~~~lean
def logMassGauge
    (K : TwoPointKernel) (hK : K.Active) : ℝ :=
  DkMath.DHNT.DUnit.logU
    (Bridge.UnitCycle.massUnit K hK)
~~~

A subtype form over ActiveKernel is acceptable if it materially reduces proof
noise, but do not create duplicate competing APIs.

Required unfolding theorem:

~~~lean
@[simp] theorem logMassGauge_eq_log_massGauge
    (K : TwoPointKernel) (hK : K.Active) :
    logMassGauge K hK = Real.log (massGauge K)
~~~

This should be definitional or nearly so.

## 2. Positivity and proof irrelevance discipline

All log interpretation theorems must use active kernels, because:

~~~text
K.Active -> 0 < massGauge K.
~~~

Do not add arbitrary fallback meanings for degenerate kernels.

Lean proof arguments hK may differ propositionally while the numeric
logMassGauge value is the same. If proof-irrelevance noise appears, isolate it
with a small theorem rather than duplicating definitions.

## 3. Log of a gauge transition

Required central theorem:

~~~lean
theorem logMassGauge_eq_add_log_factor
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active) (h2 : K2.Active) :
    logMassGauge K2 h2 =
      Real.log u + logMassGauge K1 h1
~~~

Equivalent add order is acceptable.

Use:

- MassScalesBy.factor_pos h h1 h2;
- positive/nonzero source gauge;
- Real.log_mul.

Do not require u positivity as an extra argument when it follows from the
existing transition/activity theorem.

Also expose the increment form:

~~~lean
theorem logMassGauge_sub_eq_log_factor
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active) (h2 : K2.Active) :
    logMassGauge K2 h2 - logMassGauge K1 h1
      = Real.log u
~~~

This is the preferred semantic theorem for downstream use.

## 4. Log gauge ratio

For active K1,K2 prove:

~~~lean
theorem log_massGaugeRatio
    (h1 : K1.Active) (h2 : K2.Active) :
    Real.log (massGaugeRatio K1 K2) =
      logMassGauge K2 h2 - logMassGauge K1 h1
~~~

Use Real.log_div and nonzero/positive mass gauges.

Also prove positivity of the exact ratio if useful:

~~~lean
theorem massGaugeRatio_pos
    (h1 : K1.Active) (h2 : K2.Active) :
    0 < massGaugeRatio K1 K2
~~~

Only add it if it simplifies several log proofs.

## 5. Multiplicative composition becomes additive

NumberGeometry already owns:

~~~text
massGaugeRatio K1 K3
  =
massGaugeRatio K1 K2 * massGaugeRatio K2 K3
~~~

for active K1,K2.

Under active K1,K2,K3, prove:

~~~lean
theorem log_massGaugeRatio_trans
    (h1 : K1.Active) (h2 : K2.Active) (h3 : K3.Active) :
    Real.log (massGaugeRatio K1 K3) =
      Real.log (massGaugeRatio K1 K2) +
      Real.log (massGaugeRatio K2 K3)
~~~

It is acceptable to prove this from massGaugeRatio_trans plus Real.log_mul, or
from three applications of log_massGaugeRatio and ring arithmetic.

This theorem is the formal content:

~~~text
multiplicative gauge composition -> additive log increments.
~~~

## 6. Prime step log increment

Required theorem:

~~~lean
theorem PrimeScaleStep.logMassGauge_sub_eq_log_prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1)
      - logMassGauge K1 h1
      =
    Real.log (p : ℝ)
~~~

Reuse the generic transition log theorem.

Do not re-prove primality arithmetic.

## 7. Prime-chain log increment

Strongly recommended if small:

~~~lean
theorem PrimeScaleChain.logMassGauge_sub_eq_log_prod
    {K1 K2 : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1)
      - logMassGauge K1 h1
      =
    Real.log ((ps.prod : ℕ) : ℝ)
~~~

Use h.massScalesBy_prod and the generic transition theorem.

This theorem should work for the empty chain as well.

Do not manually sum individual prime logs unless needed.

## 8. Prime-power log calibration

Optional but useful:

~~~lean
theorem PrimeScaleChain.logMassGauge_sub_eq_mul_log_prime
    {p k : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleChain K1 K2 (List.replicate k p))
    (h1 : K1.Active) :
    logMassGauge K2 (h.target_active h1)
      - logMassGauge K1 h1
      =
    (k : ℝ) * Real.log (p : ℝ)
~~~

Use:

~~~text
List.prod_replicate
Nat.cast_pow
Real.log_pow
~~~

If cast normalization becomes disproportionately noisy, defer it and retain the
general product theorem.

## 9. Distance log coordinate

Do not resurrect a separate distanceGauge core API solely for this checkpoint.

Define an analytic bridge coordinate directly from Mathlib distance:

~~~lean
def logDistanceGauge
    (K : TwoPointKernel) (hK : K.Active) : ℝ :=
  Real.log (dist K.source K.target)
~~~

The activity proof is semantically required even if the definition itself would
be total.

Required positivity helper if useful:

~~~lean
theorem dist_pos_of_active
    (K : TwoPointKernel) (hK : K.Active) :
    0 < dist K.source K.target
~~~

Reuse standard metric API.

## 10. Square mass is twice the distance log

Required theorem:

~~~lean
theorem logMassGauge_eq_two_mul_logDistanceGauge
    (K : TwoPointKernel) (hK : K.Active) :
    logMassGauge K hK =
      2 * logDistanceGauge K hK
~~~

Use:

~~~text
massGauge K = dist K.source K.target ^ 2
Real.log_pow
~~~

and the existing pairMass/distance bridge.

Do not use coordinate expansion.

## 11. Prime distance-log increment

Required target:

~~~lean
theorem PrimeScaleStep.logDistanceGauge_sub_eq_half_log_prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    logDistanceGauge K2 (h.target_active h1)
      - logDistanceGauge K1 h1
      =
    (1 / 2 : ℝ) * Real.log (p : ℝ)
~~~

Recommended proof:

1. prime mass-log increment = log p;
2. each mass log = 2 * distance log;
3. linear arithmetic.

This formalizes:

~~~text
square-mass step p
  -> distance scale sqrt(p)
  -> log-distance increment (1/2) log p.
~~~

It does not require a separate explicit theorem r2 = sqrt(p) * r1.

## 12. Optional explicit distance ratio theorem

Do not force an explicit sqrt theorem unless it is very small.

A correct target would be:

~~~text
dist K2.source K2.target
  =
Real.sqrt p * dist K1.source K1.target
~~~

under a PrimeScaleStep and active source.

Defer it if sqrt cancellation/sign bookkeeping becomes nontrivial.

## 13. Similarity log calibration — optional

NGEO-003 gives mass scaling by c^2.

If small, prove for c != 0:

~~~text
logMassGauge(mapped K) - logMassGauge(K)
  = 2 * log |c|.
~~~

Do not write 2 * log c for negative c.

This is optional.

## 14. Logs remain a bridge

Do not redefine MassScalesBy, PrimeScaleStep, or OnNatShell using logs.

The denominator-free multiplicative relations remain primary.

Logarithmic coordinates are an observer/bridge layer only.

## 15. No new no-cycle proof

NGEO-009 already owns no-cycle via strict mass growth.

Do not re-prove no-cycle through logarithms unless a tiny corollary is genuinely
useful.

## 16. Dependency constraints

Bridge/LogGauge.lean may import:

~~~text
DkMath.NumberGeometry.Bridge.UnitCycle
~~~

and narrow Mathlib analysis imports if required.

Do not import:

~~~text
DkMath.Units.NPUnit
DkMath.DHNT.UnitNatLayers
DkMath.NumberTheory.*
DkMath.CosmicFormula.*
DkMath.FLT.*
~~~

Cyclotomic and 2p phase work begins only at NGEO-011.

## 17. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/LogGaugeAxiomAudit.lean
~~~

Audit at least:

- logMassGauge_eq_add_log_factor;
- logMassGauge_sub_eq_log_factor;
- log_massGaugeRatio;
- log_massGaugeRatio_trans;
- prime step log increment;
- chain log increment if implemented;
- logMassGauge_eq_two_mul_logDistanceGauge;
- prime half-log distance theorem.

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 18. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.Bridge.LogGauge
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.LogGaugeAxiomAudit
lake build DkMath
git diff --check
~~~

Scan changed/new files for prohibited proof shortcuts and malformed docstrings.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-010.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. Final logMassGauge definition and DHNT ownership relation.
4. Generic MassScalesBy log increment theorem.
5. Log massGaugeRatio theorem.
6. Additive log composition theorem.
7. Prime-step log increment theorem.
8. Prime-chain / prime-power log theorem status.
9. Final logDistanceGauge definition.
10. Mass-log = 2 * distance-log theorem.
11. Prime half-log distance increment theorem.
12. Any explicit sqrt-distance or similarity-log theorem implemented/deferred.
13. Claims intentionally not made.
14. Build / axiom / diff-check results.
15. Exact proposed scope for NGEO-011.

Stop after NGEO-010.

Do not implement primitive 2p phases or cyclotomic/root-of-unity bridges from
NGEO-011 in the same checkpoint.
