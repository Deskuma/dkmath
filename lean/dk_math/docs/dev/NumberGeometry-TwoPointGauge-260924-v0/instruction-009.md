# NGEO-009 — DHNT Unit / UnitCycle bridge and no-cycle geometry

Branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-008.md
lean/dk_math/DkMath/NumberGeometry/GaugeTransition.lean
lean/dk_math/DkMath/NumberGeometry/PrimeScale.lean
lean/dk_math/DkMath/Units/NPUnit.lean
lean/dk_math/DkMath/UnitCycle/Core.lean
lean/dk_math/DkMath/DHNT/DHNT_Base.lean
lean/dk_math/DkMath/DHNT/UnitNatLayers.lean
~~~

## Objective

Connect NumberGeometry prime-scale gauges to the existing DkMath unit and
no-cycle infrastructure without conflating unrelated meanings of unit.

Preserve these distinctions:

1. DkMath.NP is an integer coordinate plus front/back phase bit. It is not a
   positive-real gauge unit.
2. DkMath.DHNT.Unit is a positive real value and is the natural exact bridge
   target for active mass gauges.
3. DkMath.UnitCycle.Core owns generic iteration/no-cycle logic.

NGEO-009 must formalize:

- active mass gauge as an exact DHNT positive-real Unit;
- exact ratio compatibility with massGaugeRatio;
- closed active prime-scale chain has total factor 1;
- nonempty active prime-scale chains strictly increase mass gauge and therefore
  cannot close;
- deterministic prime-scale dynamics has no nontrivial cycle, reusing
  UnitCycle theorem ownership where possible.

Do not implement logarithmic gauge coordinates yet. Those belong to NGEO-010.

## Production layout

Preferred bridge module:

~~~text
lean/dk_math/DkMath/NumberGeometry/Bridge/UnitCycle.lean
~~~

It may import:

~~~text
DkMath.NumberGeometry.PrimeScale
DkMath.DHNT.DHNT_Base
DkMath.UnitCycle.Core
~~~

Do not import NPUnit into production unless an actual mathematical use is
found. The expected audit result is that NPUnit remains separate.

Do not import DHNT.UnitNatLayers unless an exact theorem is genuinely reused.
Its floor/approximation bridges are quantization devices and must not be
silently treated as exact prime-scale maps.

If a generic ordered no-cycle theorem is missing, it is acceptable to add the
smallest generic theorem to:

~~~text
lean/dk_math/DkMath/UnitCycle/Core.lean
~~~

because generic no-cycle theorem ownership belongs there.

## 1. Active kernel subtype

A thin subtype may be introduced:

~~~lean
abbrev ActiveKernel := {K : TwoPointKernel // K.Active}
~~~

Do not change TwoPointKernel itself.

## 2. Exact DHNT mass unit

Define an exact positive-real unit from an active kernel:

~~~lean
def massUnit (K : TwoPointKernel) (hK : K.Active) : DkMath.DHNT.Unit :=
  ⟨massGauge K, (massGauge_pos_iff_active K).2 hK⟩
~~~

A subtype-based variant is acceptable if it reduces proof noise.

Expose a small simp/value theorem showing that the Unit value is exactly the
mass gauge.

Do not define another positive-real unit type.

## 3. Exact ratio orientation

NumberGeometry uses:

~~~text
massGaugeRatio K1 K2 = massGauge K2 / massGauge K1
~~~

DHNT uses:

~~~text
Unit.ratio u w = u.val / w.val
~~~

Therefore the exact orientation is target first, source second.

Required theorem:

~~~lean
theorem dhnt_ratio_massUnit
    (h1 : K1.Active) (h2 : K2.Active) :
    DkMath.DHNT.Unit.ratio
      (massUnit K2 h2)
      (massUnit K1 h1)
      =
    massGaugeRatio K1 K2
~~~

Then prove:

~~~lean
theorem dhnt_ratio_eq_factor_of_massScalesBy
    (h1 : K1.Active) (h2 : K2.Active)
    (h : MassScalesBy u K1 K2) :
    DkMath.DHNT.Unit.ratio
      (massUnit K2 h2)
      (massUnit K1 h1)
      = u
~~~

Reuse massGaugeRatio_eq_of_massScalesBy.

For a prime step, add if small:

~~~lean
theorem PrimeScaleStep.dhnt_ratio_eq_prime
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    DkMath.DHNT.Unit.ratio
      (massUnit K2 (h.target_active h1))
      (massUnit K1 h1)
      = (p : ℝ)
~~~

## 4. Ratio composition compatibility

DHNT already owns Unit.ratio_comp and NumberGeometry owns
massGaugeRatio_trans / MassScalesBy.trans.

Add at most one bridge theorem showing the orientations agree.

For active K1,K2,K3, the intended identity is:

~~~text
ratio(massUnit K3, massUnit K1)
  =
ratio(massUnit K3, massUnit K2)
*
ratio(massUnit K2, massUnit K1).
~~~

Do not duplicate the whole DHNT Unit API.

## 5. Closed chain total factor

Required theorem:

~~~lean
theorem PrimeScaleChain.closed_prod_eq_one
    (h : PrimeScaleChain K K ps)
    (hK : K.Active) :
    ps.prod = 1
~~~

Recommended proof:

1. h.massScalesBy_prod gives factor ps.prod from K to K.
2. massScalesBy_refl gives factor 1.
3. MassScalesBy.factor_unique hK gives equality of real factors.
4. recover the natural equality by exact cast.

This is the formal statement:

~~~text
closed active gauge cycle -> product of scale ratios = 1.
~~~

## 6. Prime step strict growth

Required theorem:

~~~lean
theorem PrimeScaleStep.massGauge_lt
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    massGauge K1 < massGauge K2
~~~

Use prime lower bound p >= 2, positive source mass, and the exact
MassScalesBy equation.

No coordinate proof.

## 7. Nonempty chain strict growth

Required theorem:

~~~lean
theorem PrimeScaleChain.massGauge_lt_of_nonempty
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active)
    (hne : ps ≠ []) :
    massGauge K1 < massGauge K2
~~~

Prefer induction over the chain and activity propagation.

Do not re-prove prime-product arithmetic if stepwise strictness is enough.

## 8. No nontrivial closed prime chain

Required theorem:

~~~lean
theorem PrimeScaleChain.eq_nil_of_closed_active
    (h : PrimeScaleChain K K ps)
    (hK : K.Active) :
    ps = []
~~~

This may use strict growth or closed_prod_eq_one plus prime arithmetic.

Do not introduce graph/category machinery.

## 9. Generic strict-invariant no-cycle theorem

Audit Mathlib and DkMath first.

Current UnitCycle.Core has Nat-specific no_nontrivial_cycle_of_strict, but
massGauge is real-valued.

If no generic theorem already exists, add the smallest owner theorem to
UnitCycle.Core.

Preferred shape:

~~~lean
theorem invariant_lt_iterate_of_strict
    {State Value : Type _}
    [Preorder Value]
    {T : State → State} {I : State → Value}
    (h : ∀ s, I s < I (T s)) :
    ∀ {k s}, 0 < k → I s < I (iterate T k s)

theorem no_nontrivial_cycle_of_strict_invariant
    {State Value : Type _}
    [Preorder Value]
    {T : State → State} {I : State → Value}
    (h : ∀ s, I s < I (T s)) :
    ∀ k s, iterate T k s = s → k = 0
~~~

Adjust the order typeclass only if Lean requires a slightly stronger standard
class. Do not specialize the owner theorem to Real.

Do not alter existing Nat-specific theorem names or semantics.

## 10. Deterministic prime-scale dynamics

PrimeScaleChain is a relation; UnitCycle requires a function. Do not pretend
they are identical.

Introduce an explicit deterministic selector:

~~~lean
structure PrimeScaleDynamics where
  step : ActiveKernel → ActiveKernel
  label : ActiveKernel → ℕ
  primeStep :
    ∀ K,
      PrimeScaleStep (label K) K.1 (step K).1
~~~

There is no canonical successor kernel; the structure records a chosen
dynamics.

## 11. Dynamics strict gauge

Prove:

~~~lean
theorem PrimeScaleDynamics.massGauge_strict
    (D : PrimeScaleDynamics) (K : ActiveKernel) :
    massGauge K.1 < massGauge (D.step K).1
~~~

Reuse PrimeScaleStep.massGauge_lt.

## 12. UnitCycle no-cycle bridge

Instantiate the generic UnitCycle theorem with:

~~~text
State = ActiveKernel
T = D.step
Value = ℝ
I(K) = massGauge K.1
~~~

Required theorem:

~~~lean
theorem PrimeScaleDynamics.no_nontrivial_cycle
    (D : PrimeScaleDynamics) :
    ∀ k K,
      DkMath.UnitCycle.iterate D.step k K = K →
      k = 0
~~~

This is the exact deterministic bridge:

~~~text
strictly expanding positive gauge -> no nontrivial cycle.
~~~

If a suitable generic UnitCycle theorem already exists, reuse it instead of
adding another.

## 13. UnitNatLayers audit

DkMath.DHNT.UnitNatLayers.Bridge maps a positive-real Unit into Nat using
chosen functions such as constant 1, floor, scaled floor, or sqrt/floor
approximations.

These are quantization bridges, not exact NumberGeometry scale identities.

The expected result is:

~~~text
DHNT.Unit from DHNT_Base: exact bridge
DHNT.UnitNatLayers.Bridge: audited, not required for exact v0 bridge
~~~

If an exact reusable theorem is found, it may be used but must be justified.

## 14. NPUnit audit

DkMath.NP models front/back half-lattice succession.

Do not identify NP with massUnit, PrimeScaleStep, or massGaugeRatio.

Record the separation explicitly in report-009.md.

## 15. False claims to avoid

Do not claim:

- every MassScalesBy relation determines a deterministic next kernel;
- PrimeScaleChain is itself a Function.iterate orbit;
- DHNT floor bridges preserve exact prime factors;
- NPUnit is the positive-real gauge unit;
- every positive real scale greater than one is prime;
- no-cycle results imply prime distribution, cyclotomic results, or FLT.

## 16. Dependency constraints

Bridge production code may import only the exact modules needed from:

~~~text
DkMath.NumberGeometry.PrimeScale
DkMath.DHNT.DHNT_Base
DkMath.UnitCycle.Core
~~~

Do not import FLT, NumberTheory, or CosmicFormula into this bridge.

Logarithmic gauge coordinates remain NGEO-010.

## 17. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/UnitCycleBridgeAxiomAudit.lean
~~~

Audit:

- DHNT ratio bridge;
- closed chain product theorem;
- strict prime step/chain theorems;
- generic UnitCycle strict-invariant theorem if new;
- deterministic prime-scale no-cycle theorem.

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
lake build DkMath.UnitCycle.Core
lake build DkMath.NumberGeometry.Bridge.UnitCycle
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.UnitCycleBridgeAxiomAudit
lake build DkMath
git diff --check
~~~

Adjust the bridge module path only if the final filename differs.

Scan changed/new files for prohibited shortcuts and malformed docstrings.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-009.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. NPUnit audit conclusion.
4. DHNT.Unit and UnitNatLayers audit conclusion.
5. Final massUnit API.
6. Exact DHNT ratio orientation theorem.
7. Closed prime-chain product=1 theorem.
8. Prime step/chain strict-growth theorems.
9. No-nonempty-closed-chain theorem.
10. Whether UnitCycle.Core already had a generic ordered theorem or received one.
11. Final PrimeScaleDynamics representation.
12. Exact UnitCycle no-cycle bridge theorem.
13. Claims intentionally not made.
14. Build / axiom / diff-check results.
15. Exact proposed scope for NGEO-010.

Stop after NGEO-009.

Do not implement logarithmic gauge coordinates from NGEO-010 in the same
checkpoint.
