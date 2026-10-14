# GCNB-006 / instruction-004 — Cyclotomic ideal norm ↔ TraceOne shadow compatibility

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-003.md
- DkMath/Lib/Cosmic/GTailCyclotomic.lean
- DkMath/CFBRC/CyclotomicIdeal.lean
- DkMath/FLT/Prime/PrimeCyclotomicIdeal.lean
- DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean
- DkMath/FLT/Prime/PrimeTraceOneCoordinateCoprime.lean
- DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean

## 1. Mission

The branch now has two independently checked representations of the same
prime cyclotomic shell.

Full cyclotomic carrier:

~~~text
alpha = (g+u) - zeta*u
I_alpha = (alpha)

Ideal.absNorm I_alpha = GN p g u = GTail p 1 g u.
~~~

TraceOne shadow:

~~~text
C = P.coord (g+u) u

TraceOne.norm C =
  GTailCyclotomicShell p g u.
~~~

GCNB-006 must prove the exact scalar compatibility between these two
representations.

The intended central identity is:

~~~text
TraceOne.norm (P.coord (g+u) u)
  =
(Int.ofNat (Ideal.absNorm I_alpha)).
~~~

Equivalently at the nonnegative level:

~~~text
Int.natAbs (TraceOne.norm (P.coord (g+u) u))
  =
Ideal.absNorm I_alpha.
~~~

This is a **norm-level compatibility theorem**.

It is not an equality of algebraic elements, an equality of ideals, or a map
from the full cyclotomic field into TraceOneInt.

## 2. First cleanup: remove the stale nonzero-gap hypothesis

The neutral theorem

~~~lean
DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell
    {p g u : Nat} (hg : g != 0) :
    ((GTail p 1 g u : Nat) : Int) =
      GTailCyclotomicShell p (g : Int) (u : Int)
~~~

still carries an old proof-path hypothesis g != 0.

GCNB-001 already proved the stronger polynomial identity

~~~lean
GTail_one_eq_GTailCyclotomicShell
    {R} [CommSemiring R] (d : Nat) (x u : R)
~~~

without cancellation or nonzero assumptions.

Refactor the Nat/Int bridge so its canonical API is unconditional:

~~~lean
theorem natCast_GTail_one_eq_GTailCyclotomicShell
    {p g u : Nat} :
    ((GTail p 1 g u : Nat) : Int) =
      GTailCyclotomicShell p (g : Int) (u : Int)
~~~

Keep an optional compatibility wrapper with suffix _of_ne_zero if source
compatibility requires it.

Prefer a direct cast/polynomial proof. Do not route through Q and field
cancellation unless unavoidable.

Required regression:

~~~text
g = 0
u = 0
g = u = 0
~~~

must elaborate.

## 3. Recommended adapter module

Prefer a new FLT-prime adapter:

~~~text
DkMath/FLT/Prime/PrimeCyclotomicTraceOne.lean
~~~

with dependency direction:

~~~text
CFBRC cyclotomic ideal
        +
NumberTheory TraceOne coordinate packet
        ↓
FLT.Prime compatibility adapter
~~~

Do not add CFBRC -> FLT or NumberTheory -> FLT reverse dependencies.

## 4. Core norm compatibility theorem

Let:

~~~text
P : PrimeTraceOneCoordinatePacket K p zeta hzeta
~~~

and natural g,u.

Prove a theorem of the conceptual form:

~~~lean
theorem PrimeTraceOneCoordinatePacket.coord_norm_eq_cyclotomicIdeal_absNorm
    ...
    (P : PrimeTraceOneCoordinatePacket K p zeta hzeta)
    (g u : Nat) :
    norm (P.coord ((g + u : Nat) : Int) (u : Int)) =
      (Ideal.absNorm
        (cyclotomicLinearFactorIdeal hzeta g u) : Int)
~~~

Use:

~~~text
P.coord_norm_eq
natCast_GTail_one_eq_GTailCyclotomicShell
cyclotomicLinearFactorIdeal_absNorm_eq_GN
GN = GTail p 1
~~~

Do not recompute QR/QNR products or field norms.

This theorem should not require g != 0 after the cleanup in section 2.

## 5. Nonnegative compatibility theorem

Also expose the exact Nat-valued equality:

~~~text
Int.natAbs
  (norm (P.coord (g+u) u))
=
Ideal.absNorm (cyclotomicLinearFactorIdeal hzeta g u).
~~~

This is useful because both the FLT Prime packet and ideal valuation APIs are
Nat-facing.

If the Int equality immediately implies the natAbs equality by simp, keep the
proof thin.

## 6. Global rational-prime divisibility/valuation compatibility

From the natAbs equality, expose scalar compatibility such as:

~~~text
q divides natAbs(TraceOne.norm C)
  <->
q divides Ideal.absNorm I_alpha
~~~

and:

~~~text
padicValNat q (natAbs(TraceOne.norm C))
  =
padicValNat q (Ideal.absNorm I_alpha).
~~~

These are global rational-prime statements only.

Do not claim a correspondence between a prime ideal in O_K and a prime ideal
in TraceOneInt.

## 7. PrimeAdicFactorPacket specialization

For:

~~~text
P0 : PrimeAdicFactorPacket p g u x
P  : PrimeTraceOneCoordinatePacket K p zeta hzeta
~~~

prove the stable FLT-facing compatibility:

~~~text
norm (P.coord (g+u) u)
  =
(Ideal.absNorm I_alpha : Int)
  =
(GTail p 1 g u : Nat cast to Int).
~~~

Then derive:

~~~text
Int.natAbs (norm (P.coord (g+u) u))
  = Ideal.absNorm I_alpha

g * Int.natAbs (norm (P.coord (g+u) u))
  = x^p.
~~~

Reuse the existing:

~~~text
P0.gap_mul_cyclotomicIdeal_absNorm_eq_pow
~~~

rather than reconstructing the FLT equation.

## 8. Ramified PrimeAdicPowerSplit specialization

For:

~~~text
S : PrimeAdicPowerSplit p g u x
P : PrimeTraceOneCoordinatePacket K p zeta hzeta
~~~

transport the already-proved ideal norm normal form:

~~~text
Int.natAbs (norm (P.coord (g+u) u))
  = p * S.b^p.
~~~

Also expose the rational-prime valuation:

~~~text
padicValNat p
  (Int.natAbs (norm (P.coord (g+u) u)))
  = 1.
~~~

This is only scalar transport. It is **not** the later discrAxis stripping
theorem and should not duplicate PrimeTraceOneStrippedIdeal.

## 9. Compatibility with existing PrimeTraceOneStrippedIdeal

Audit the private theorem:

~~~text
parent_norm_eq_natCast_residual
~~~

in PrimeTraceOneStrippedIdeal.lean.

If the new public compatibility theorem can replace its local Nat/Int shell
conversion with a one-line reuse, refactor it.

Do not otherwise expand or redesign PrimeTraceOneStrippedIdeal in this
checkpoint.

The goal is to make the new public bridge the canonical source of the common
norm value.

## 10. Critical firewall

The following are **not** consequences of GCNB-006:

~~~text
cyclotomicLinearFactorInRingOfIntegers = TraceOne coord
cyclotomicLinearFactorIdeal = Ideal.span {TraceOne coord}
O_K is isomorphic to TraceOneInt
a prime ideal above q on one side corresponds to a prime ideal on the other
class-group data is preserved
p-th-power ideal roots are preserved
~~~

The TraceOne coordinate is a quadratic shadow constructed from the QR/QNR
Gauss decomposition. The full cyclotomic carrier has degree p-1 in general.

Only checked scalar norm identities may be transported automatically.

## 11. Optional provenance theorem

If cheap, add a theorem/comment showing that both equalities meet at the same
canonical shell:

~~~text
Ideal.absNorm I_alpha
  <- GN / GTail ->
GTailCyclotomicShell
  <- TraceOne.norm coord.
~~~

Do not create a new large structure merely to record this diagram.

## 12. Tests

Add a focused test module, suggested:

~~~text
DkMathTest/FLT/Prime/PrimeCyclotomicTraceOne.lean
~~~

Required checks:

1. unconditional Nat/Int bridge at g = 0;
2. generic coord norm = cast ideal absNorm;
3. generic natAbs coord norm = ideal absNorm;
4. generic rational-prime valuation equality;
5. PrimeAdicFactorPacket complete power identity through TraceOne natAbs norm;
6. PrimeAdicPowerSplit normal form p * b^p through TraceOne natAbs norm;
7. p = 3, 5, 7 coordinate-packet calibration using canonical CyclotomicField;
8. #print axioms for every new public theorem.

Do not invent FLT counterexamples for tests.

## 13. Validation

Run at least:

~~~text
lake build DkMath.Lib.Cosmic.GTailCyclotomic
lake build DkMath.FLT.Prime.PrimeCyclotomicTraceOne
lake build DkMathTest.FLT.Prime.PrimeCyclotomicTraceOne
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
lake build DkMath.FLT.Prime
lake build DkMath.CFBRC
lake build DkMath
git diff --check
~~~

No:

~~~text
sorry
admit
sorryAx
new axiom
unsafe proof shortcut
~~~

The pre-existing ZsigmondyCyclotomicResearch warning is outside this
checkpoint.

## 14. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-004.md
~~~

Classify:

### Outcome A — norm-level cyclotomic/TraceOne compatibility complete

The full carrier ideal absNorm and TraceOne coordinate norm are proved to be
the same scalar, including Nat-valued and valuation-facing forms, and the FLT
Prime packet specializes cleanly.

### Outcome B — scalar equality complete, old Nat/Int helper remains conditional

The main FLT packet bridge works using g > 0, but the fully unconditional
g = 0 Nat/Int bridge could not be extracted cleanly. Record the exact reason.

### Outcome C — TraceOne compatibility exposes a genuine representation gap

Do not assert an element/ideal map. Record exactly which scalar theorem is
available and which stronger relation lacks a checked construction.

## 15. Completion gate

GCNB-006 is complete when the following checked diagram exists:

~~~text
                    GTail / GN
                   /          \
                  /            \
Ideal.absNorm(I_alpha)      TraceOne.norm(coord)
                  \            /
                   \          /
                    same scalar
~~~

and the PrimeAdicFactorPacket / PrimeAdicPowerSplit arithmetic can be read on
either scalar side without changing its content.

After this, perform p=3/5/7 calibration (GCNB-008) and then reassess whether
GCNB-004L supplies a genuinely new FLT7 re-entry theorem.
