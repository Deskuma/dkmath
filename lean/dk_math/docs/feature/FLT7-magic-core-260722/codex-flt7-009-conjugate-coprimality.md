# FLT7-009 — Primitive conjugate coprimality and element-level seventh-power normal forms

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Use the current branch HEAD after completed FLT7-008.

## Objective

Prove that primitive seventh-cyclotomic coordinates have no common conjugate
factor except the ramified axis `sevenAxis`.

Then eliminate that exceptional factor separately in the two counterexample
routes:

```text
Away:      7 ∤ z-y
           cyclotomic coordinate and its conjugate are coprime
           cyclotomic coordinate = gamma^7

Ramified:  7 ∣ z-y
           cyclotomic coordinate = sevenAxis * residualCore
           residualCore and its conjugate are coprime
           residualCore = gamma^7
```

The resulting route-level normal forms are

```text
Away:      C7(z,y) = gamma^7
Ramified:  C7(z,y) = sevenAxis * gamma^7.
```

This checkpoint must stop at these element-level normal forms. Do not begin a
coordinate descent or claim FLT7.

## New modules

Create:

```text
DkMath/FLT/Seven/PrimitiveCoordinateCoprime.lean
DkMath/FLT/Seven/QuadraticConjugateCoprime.lean
DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean
```

Suggested imports:

```lean
-- PrimitiveCoordinateCoprime.lean
import DkMath.FLT.Seven.QuadraticCoprimeFactor

-- QuadraticConjugateCoprime.lean
import DkMath.FLT.Seven.PrimitiveCoordinateCoprime

-- QuadraticSeventhPowerNormalForm.lean
import DkMath.FLT.Seven.QuadraticConjugateCoprime
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenPrimitiveCoordinateCoprime.lean
DkMathTest/FLT/SevenQuadraticSeventhPowerNormalForm.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-009.md
```

Use namespace:

```lean
namespace DkMath.FLT.Seven
```

# Part A — Primitive integer coordinate pair

The cyclotomic coordinate is

```text
A = z^3 + z^2*y - y^3,
B = -z^2*y - z*y^2 = -z*y*(z+y).
```

Prove that coprime natural endpoints produce coprime integer coordinates.

First isolate the prime-divisor elimination theorem. One acceptable surface is:

```lean
theorem prime_dvd_both_cyclotomicSeven_coordinates
    {z y q : ℕ}
    (hq : Nat.Prime q)
    (hA : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ))
    (hB : (q : ℤ) ∣ cyclotomicSevenSnd (z : ℤ) (y : ℤ)) :
    q ∣ z ∧ q ∣ y
```

Recommended proof architecture:

1. move the two coordinate equations to `ZMod q`;
2. use

```text
B = -z*y*(z+y);
```

3. split the zero product into `z=0`, `y=0`, or `z+y=0`;
4. in each case, the equation `A=0` forces the other endpoint to vanish;
5. return to natural divisibility.

This proof works uniformly at `q=2` and `q=7`; do not use residue enumeration.

Then prove the stable coprimality theorem:

```lean
theorem cyclotomicSeven_coordinates_isCoprime
    {z y : ℕ}
    (hcop : Nat.Coprime z y) :
    IsCoprime
      (cyclotomicSevenFst (z : ℤ) (y : ℤ))
      (cyclotomicSevenSnd (z : ℤ) (y : ℤ))
```

If the local `IsCoprime` API over `ℤ` is awkward, an equivalent theorem
providing explicit Bézout coefficients is acceptable:

```lean
∃ m n : ℤ,
  m * cyclotomicSevenFst (z : ℤ) (y : ℤ) +
  n * cyclotomicSevenSnd (z : ℤ) (y : ℤ) = 1
```

Expose one of these as public API; keep any conversion helper local.

Add the packet specialization:

```lean
theorem counterexample_cyclotomicSeven_coordinates_isCoprime
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    IsCoprime
      (cyclotomicSevenFst (z : ℤ) (y : ℤ))
      (cyclotomicSevenSnd (z : ℤ) (y : ℤ))
```

Use `coprime_y_z_of_counterexamplePack` and symmetry.

# Part B — Generic exceptional-divisor support

For `w : TraceOneInt (-2)`, prove the exact conjugate-difference identity:

```lean
theorem sub_conj_eq_snd_mul_sevenAxis
    (w : TraceOneInt (-2)) :
    w - conj w = (w.snd : TraceOneInt (-2)) * sevenAxis
```

Prove the companion identity that extracts the first coordinate after
multiplication by the axis:

```lean
theorem sevenAxis_mul_sub_tau_mul_sub_conj
    (w : TraceOneInt (-2)) :
    sevenAxis * w - tau (-2) * (w - conj w) =
      (w.fst : TraceOneInt (-2)) * sevenAxis
```

Equivalent reassociation/cast notation is acceptable.

Now prove the generic support theorem:

```lean
theorem common_divisor_dvd_sevenAxis_of_coordinate_coprime
    {w d : TraceOneInt (-2)}
    (hcoords : IsCoprime w.fst w.snd)
    (hdw : d ∣ w)
    (hdconj : d ∣ conj w) :
    d ∣ sevenAxis
```

Proof architecture:

1. from `d∣w` and `d∣conj w`, obtain

```text
d ∣ w-conj w = w.snd * sevenAxis;
```

2. multiply and subtract using the companion identity to obtain

```text
d ∣ w.fst * sevenAxis;
```

3. extract Bézout coefficients `m,n` from `IsCoprime w.fst w.snd`;
4. combine the two divisibilities to obtain

```text
d ∣ (m*w.fst+n*w.snd)*sevenAxis = sevenAxis.
```

Then specialize to the cyclotomic coordinate:

```lean
theorem common_divisor_cyclotomic_conj_dvd_sevenAxis
    {z y : ℕ} {d : TraceOneInt (-2)}
    (hcop : Nat.Coprime z y)
    (hd : d ∣ cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
    (hdc : d ∣ conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))) :
    d ∣ sevenAxis
```

# Part C — The ramified axis is prime

Prove:

```lean
theorem irreducible_sevenAxis :
    Irreducible (sevenAxis : TraceOneInt (-2))
```

Use only:

```text
norm sevenAxis = 7,
norm(x*y)=norm x * norm y,
nonzero norm ≥ 1,
unit iff norm = 1,
7 is prime in ℤ/ℕ.
```

If `sevenAxis=a*b`, positivity forces one factor norm to be `1`, hence that
factor is a unit.

Then expose primality through the Euclidean/GCD infrastructure:

```lean
theorem prime_sevenAxis :
    Prime (sevenAxis : TraceOneInt (-2))
```

Use the current Mathlib bridge from irreducible to prime in a Euclidean domain.

Required terminal elimination lemma:

```lean
theorem isUnit_of_dvd_sevenAxis_of_dvd_terminal
    {d r : TraceOneInt (-2)}
    (hdAxis : d ∣ sevenAxis)
    (hdr : d ∣ r)
    (hterminal : ¬ sevenAxis ∣ r) :
    IsUnit d
```

A divisor of the prime `sevenAxis` is either a unit or associated to it. The
associated case would imply `sevenAxis∣r`, contradicting terminality.

# Part D — Away-route conjugate coprimality

For primitive endpoints away from the gap channel, prove:

```lean
theorem cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap
    {z y : ℕ}
    (hcop : Nat.Coprime z y)
    (hgap : ¬ 7 ∣ z-y) :
    IsUnit
      (gcd
        (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))
        (conj (cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ))))
```

Architecture:

1. the gcd divides the coordinate and its conjugate;
2. primitive coordinate support says it divides `sevenAxis`;
3. if it were nonunit, primality would force `sevenAxis` to divide the
   cyclotomic coordinate;
4. use the existing one-layer criterion

```text
sevenAxis ∣ cyclotomic coordinate ↔ 7 ∣ z-y
```

and contradict `hgap`.

Now consume the away natural power split.

Required theorem:

```lean
theorem exists_cyclotomicSeven_eq_seventh_power_of_away
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hgap : ¬ 7 ∣ z-y) :
    ∃ gamma : TraceOneInt (-2),
      cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = gamma ^ 7
```

Suggested route:

1. obtain `v` with

```text
GN 7 (z-y) y = v^7
```

from `branchAway_seventh_power_factor_split`;
2. use the GN/cyclotomic norm bridge to prove

```text
C * conj C = (v : TraceOneInt (-2))^7;
```

3. apply `exists_eq_seventh_power_of_coprime_mul_eq_pow` from FLT7-008 to
   `C` and `conj C`.

# Part E — Ramified residual conjugate coprimality

For a terminal residual packet, prove:

```lean
theorem SevenQuadraticResidualPacket.gcd_residual_conj_isUnit
    {x y z : ℕ}
    (q : SevenQuadraticResidualPacket x y z) :
    IsUnit (gcd q.residualCore (conj q.residualCore))
```

Architecture:

1. let `d = gcd residualCore (conj residualCore)`;
2. `d` divides both residual factors;
3. multiply by `sevenAxis` and use `q.coordinate_eq` plus
   `conj_sevenAxis` to show `d` divides the full cyclotomic coordinate and its
   conjugate;
4. primitive endpoint coordinate support gives `d∣sevenAxis`;
5. `d∣residualCore` and `q.residual_terminal` force `d` to be a unit.

Then prove the element-level seventh-power theorem:

```lean
theorem SevenQuadraticResidualPacket.exists_residualCore_eq_seventh_power
    {x y z : ℕ}
    (q : SevenQuadraticResidualPacket x y z) :
    ∃ gamma : TraceOneInt (-2),
      q.residualCore = gamma ^ 7
```

Use:

```text
residualCore * conj residualCore
  = norm residualCore
  = b^7
```

and the exact coprime factor extraction from FLT7-008.

# Part F — Normal-form packets

Define the ramified element-level packet:

```lean
structure SevenQuadraticSeventhPowerPacket (x y z : ℕ) : Type where
  residual : SevenQuadraticResidualPacket x y z
  root : TraceOneInt (-2)
  residual_eq : residual.residualCore = root ^ 7
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) =
      sevenAxis * root ^ 7
```

Prove:

```lean
theorem nonempty_sevenQuadraticSeventhPowerPacket_of_residual
    {x y z : ℕ}
    (q : SevenQuadraticResidualPacket x y z) :
    Nonempty (SevenQuadraticSeventhPowerPacket x y z)
```

and expose chosen constructors:

```lean
noncomputable def sevenQuadraticSeventhPowerPacket_of_residual ...
noncomputable def sevenQuadraticSeventhPowerPacket_of_counterexample ...
```

Define the final two-route algebraic classification:

```lean
inductive QuadraticCounterexampleRoute (x y z : ℕ) : Type
  | away
      (seven_not_dvd_gap : ¬ 7 ∣ z-y)
      (root : TraceOneInt (-2))
      (coordinate_eq :
        cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7)
  | ramified
      (packet : SevenQuadraticSeventhPowerPacket x y z)
```

Prove the checkpoint summit:

```lean
theorem quadraticCounterexampleRoute_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (QuadraticCounterexampleRoute x y z)
```

This theorem may perform a classical case split on `7∣z-y`.

# Tests

The focused tests must cover abstract wiring only:

- prime common divisor elimination for the two cubic coordinates;
- coordinate Bézout/coprimality extraction;
- the two generic conjugate identities;
- exceptional-divisor support `d∣sevenAxis`;
- `sevenAxis` irreducible/prime and terminal divisor elimination;
- away-route gcd unit and seventh-power coordinate form;
- ramified residual gcd unit and seventh-power residual form;
- both constructors of `QuadraticCounterexampleRoute`.

Do not instantiate an actual counterexample.
Avoid `native_decide`.

# Required report

Record:

- exact theorem/definition/structure surface;
- the ZMod proof of primitive coordinate coprimality;
- the two coordinate/conjugate identities;
- the Bézout proof that every common divisor divides `sevenAxis`;
- irreducibility and primality of `sevenAxis`;
- away-route conjugate coprimality and exact seventh-power form;
- ramified terminal residual conjugate coprimality;
- promotion from seventh-power norm to element-level seventh power;
- the final two-route algebraic classification;
- recommended FLT7-010 boundary.

The recommended FLT7-010 boundary should expand the two element-level normal
forms into explicit coordinate equations for a seventh power

```text
(u+v*tau)^7
```

and identify the finite sign/unit sector. Since all units are already absorbed,
the next obstruction must come from the coordinate equations or a strict
transformation, not from a hidden unit class.

# Non-goals

Do not add:

- a coordinate descent;
- an FLT7 contradiction or no-solution theorem;
- a general cyclotomic coprimality theorem for arbitrary primes;
- ideal or class-number theory;
- new unit sectors beyond `±1`;
- changes to FLT3 or FLT5.

# Outcome classification

- Outcome A: primitive coordinate coprimality, exceptional support,
  `sevenAxis` primality, both route coprimality results, and exact
  element-level seventh-power normal forms are complete.
- Outcome B: exceptional support and one route are complete, but the second
  route or route packet needs a clearly identified follow-up.
- Outcome C: primitive coordinate coprimality or exceptional support is false;
  report the explicit arithmetic counterexample and preserve FLT7-008.

Commit with a focused message and push to the current feature branch.
