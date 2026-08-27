# FLT7-006 — Primitive counterexample packet and seven-adic routing

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Current completed checkpoint:

```text
95b79d98 Add FLT7 primitive single-layer saturation
```

## Objective

Introduce the positive primitive FLT7 counterexample packet and route every
candidate through the factorization

```text
x^7 = (z-y) * GN 7 (z-y) y.
```

The checkpoint must expose two exact branches.

### Away from seven

```text
7 ∤ z-y
```

Then the gap and `GN 7` factor are coprime, so their product being a seventh
power forces both factors to be seventh powers.

### Ramified seven branch

```text
7 ∣ z-y
```

Then primitive endpoint coprimality and FLT7-005 force

```text
v₇(GN 7 (z-y) y) = 1,
v₇(z-y) = 6 mod 7,
7^6 ∣ z-y.
```

Package this arithmetic output without attempting a complete descent or a
no-solution theorem.

This checkpoint is routing only. It must not claim that either branch is
already contradictory.

## New modules

Create:

```text
DkMath/FLT/Seven/Basic.lean
DkMath/FLT/Seven/CounterexampleRouting.lean
```

Suggested imports:

```lean
-- Basic.lean
import Mathlib

-- CounterexampleRouting.lean
import DkMath.FLT.Seven.PrimitiveCyclotomicDepth
import DkMath.FLT.Seven.Basic
```

Using `DkMath.FLT.Core` for the generic GN factor identity is acceptable if it
keeps the proof short and does not introduce a circular import. Otherwise prove
the exponent-seven specialization locally.

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenCounterexampleRouting.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-006.md
```

## Part A — Basic FLT7 packet

In namespace:

```lean
namespace DkMath.FLT.Seven
```

Define:

```lean
def Fermat7Equation (x y z : ℕ) : Prop :=
  x ^ 7 + y ^ 7 = z ^ 7
```

Define the primitive positive packet:

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat7Equation x y z
```

This mirrors the local FLT5 packet but remains entirely inside
`DkMath.FLT.Seven`.

Required elementary theorems:

```lean
theorem seventh_sub_eq_of_add_eq
    {x y z : ℕ}
    (hEq : Fermat7Equation x y z) :
    z ^ 7 - y ^ 7 = x ^ 7
```

```lean
theorem right_lt_of_fermat7Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat7Equation x y z) :
    y < z
```

```lean
theorem gap_pos_of_fermat7Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat7Equation x y z) :
    0 < z - y
```

Derive primitive endpoint coprimality:

```lean
theorem coprime_y_z_of_counterexamplePack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nat.Coprime y z
```

```lean
theorem coprime_gap_y_of_counterexamplePack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y
```

Use the same prime-divisor argument as the established FLT5 local packet; do
not import FLT5.

## Part B — Exact GN7 body

Expose the natural body:

```lean
def Body7 (g y : ℕ) : ℕ :=
  g * GN 7 g y
```

Required factor theorem:

```lean
theorem body7_eq_seventh_power_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Body7 (z - y) y = x ^ 7
```

Also prove positivity/nonzero facts needed by valuation APIs:

```lean
theorem GN_seven_pos_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    0 < GN 7 (z - y) y
```

```lean
theorem body7_ne_zero_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Body7 (z - y) y ≠ 0
```

Derive positivity from the factor equation and the positive gap rather than
re-expanding every GN term unless a direct proof is shorter.

## Part C — Common-divisor control

Prove the natural GN7 exceptional-term decomposition:

```lean
theorem GN_seven_eq_gap_mul_add_seven_mul_y_pow_six
    (g y : ℕ) :
    GN 7 g y =
      g * (g ^ 5 + 7 * g ^ 4 * y + 21 * g ^ 3 * y ^ 2
        + 35 * g ^ 2 * y ^ 3 + 35 * g * y ^ 4 + 21 * y ^ 5)
        + 7 * y ^ 6
```

Equivalent reassociation is acceptable.

From this, prove that primitive common divisors are supported only at `7`:

```lean
theorem gcd_gap_GN_seven_dvd_seven
    {g y : ℕ}
    (hcop : Nat.Coprime g y) :
    Nat.gcd g (GN 7 g y) ∣ 7
```

Suggested architecture:

1. the gcd divides `g` and `GN 7 g y`;
2. the decomposition shows it divides `7*y^6`;
3. coprimality with `y`, hence with `y^6`, removes the endpoint factor;
4. conclude it divides `7`.

Then obtain the exact branch values.

```lean
theorem gcd_gap_GN_seven_eq_one_of_not_seven_dvd
    {g y : ℕ}
    (hcop : Nat.Coprime g y)
    (h7g : ¬ 7 ∣ g) :
    Nat.gcd g (GN 7 g y) = 1
```

```lean
theorem gcd_gap_GN_seven_eq_seven_of_seven_dvd
    {g y : ℕ}
    (hcop : Nat.Coprime g y)
    (h7g : 7 ∣ g) :
    Nat.gcd g (GN 7 g y) = 7
```

For the ramified direction, use FLT7-005 to obtain `7 ∣ GN 7 g y` after
specializing to endpoint pair `(g+y,y)`, or prove the short equivalent bridge
carefully. Do not assume the result without connecting the coordinate
convention.

Add packet-specialized aliases:

```lean
theorem branchAway_coprime_gap_GN_seven
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 7 ∣ z - y) :
    Nat.Coprime (z - y) (GN 7 (z - y) y)
```

```lean
theorem branchRamified_gcd_gap_GN_seven
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    Nat.gcd (z - y) (GN 7 (z - y) y) = 7
```

## Part D — Away-from-seven power split

Prove the generic natural factor split at exponent seven:

```lean
theorem seventh_power_factor_split
    {a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ 7) :
    (∃ u : ℕ, a = u ^ 7) ∧
    (∃ v : ℕ, b = v ^ 7)
```

Use the existing `exists_eq_pow_of_mul_eq_pow` infrastructure as in FLT5, but
do not import FLT5.

Then prove the branch normal form:

```lean
theorem branchAway_seventh_power_factor_split
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 7 ∣ z - y) :
    (∃ u : ℕ, z - y = u ^ 7) ∧
    (∃ v : ℕ, GN 7 (z - y) y = v ^ 7)
```

This theorem is a routing output, not a contradiction.

## Part E — Ramified seven-adic packet

First prove the primitive endpoint exclusions:

```lean
theorem not_seven_dvd_y_of_counterexample_of_seven_dvd_gap
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    ¬ 7 ∣ y
```

```lean
theorem seven_dvd_x_of_counterexample_of_seven_dvd_gap
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    7 ∣ x
```

The first follows from coprimality of gap and `y`; the second follows from the
body factor equation and divisibility of the gap.

Prove the exact residual valuation by reusing FLT7-005:

```lean
theorem padicValNat_GN_seven_eq_one_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    padicValNat 7 (GN 7 (z - y) y) = 1
```

Generalize the elementary valuation arithmetic used in FLT5 to exponent seven:

```lean
theorem padicValNat_carrier_shape_of_mul_eq_seventh
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 7)
    (hrVal : padicValNat 7 residual = 1) :
    ∃ m : ℕ,
      padicValNat 7 carrier = 6 + 7 * m
```

The proof should use:

```text
v₇(carrier) + 1 = 7 * v₇(distinguished).
```

Do not use subtraction in integers if the natural-number rearrangement from the
FLT5 proof pattern is cleaner.

Apply it to the counterexample body:

```lean
theorem padicValNat_gap_shape_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    ∃ m : ℕ,
      padicValNat 7 (z - y) = 6 + 7 * m
```

Then expose the fixed-thickness consequence:

```lean
theorem seven_pow_six_dvd_gap_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    7 ^ 6 ∣ z - y
```

Use `padicValNat_dvd_iff_le` with the positive/nonzero gap.

## Required packet

Define a proof packet for the ramified branch. Since the carrier and residual
are fixed by `(x,y,z)`, a `Prop` structure is sufficient.

```lean
structure SevenAdicCounterexamplePacket (x y z : ℕ) : Prop where
  counterexample : CounterexamplePack x y z
  seven_dvd_gap : 7 ∣ z - y
  factor_eq : (z - y) * GN 7 (z - y) y = x ^ 7
  gcd_eq_seven : Nat.gcd (z - y) (GN 7 (z - y) y) = 7
  seven_not_dvd_y : ¬ 7 ∣ y
  seven_dvd_x : 7 ∣ x
  residual_padicValNat : padicValNat 7 (GN 7 (z - y) y) = 1
  gap_padicValNat_shape :
    ∃ m : ℕ, padicValNat 7 (z - y) = 6 + 7 * m
  seven_pow_six_dvd_gap : 7 ^ 6 ∣ z - y
```

Prove construction:

```lean
theorem sevenAdicCounterexamplePacket_of_branch
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) :
    SevenAdicCounterexamplePacket x y z
```

## Route classification

Define a small routing proposition or inductive type. One acceptable form is:

```lean
inductive CounterexampleRoute (x y z : ℕ) : Prop
  | away
      (hnot : ¬ 7 ∣ z - y)
      (gapPow : ∃ u : ℕ, z - y = u ^ 7)
      (gnPow : ∃ v : ℕ, GN 7 (z - y) y = v ^ 7)
  | ramified
      (packet : SevenAdicCounterexamplePacket x y z)
```

Prove:

```lean
theorem counterexampleRoute_of_pack
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    CounterexampleRoute x y z
```

This is the checkpoint summit. It must classify a primitive candidate without
claiming that either route is impossible.

## Tests

The focused test should verify theorem wiring rather than search for an actual
counterexample.

Include:

- construction of `Body7` and the factor theorem from a hypothetical packet;
- away-branch factor splitting under abstract packet hypotheses;
- ramified packet construction under abstract packet hypotheses;
- extraction of `7^6 ∣ z-y` from the ramified packet;
- route elimination/case analysis showing both constructors expose their
  intended data.

Do not attempt to instantiate a real `CounterexamplePack`.
Avoid `native_decide`.

## Required report

Record:

- exact theorem and definition surface;
- primitive endpoint coprimality derivation;
- common-divisor support at `7`;
- exact gcd values in both branches;
- away-branch seventh-power splitting;
- residual valuation `1` and carrier valuation `6 mod 7`;
- the `7^6` fixed-thickness consequence;
- packet and route-classification construction;
- recommended FLT7-007 boundary.

The recommended next boundary should strip the ramifier in the exceptional
packet and derive a coprime seventh-power factor pair, or design the quadratic
order factorization consumed by both routes. Do not claim a descent until the
new residual coordinate packet and its strict measure are explicit.

## Non-goals

Do not add:

- an FLT7 no-solution theorem;
- a contradiction from either route;
- a complete descent;
- general LTE;
- ideals, PID, UFD, Euclidean, or class-number theory;
- a general prime-exponent abstraction;
- primitive-prime providers for arbitrary factors;
- changes to FLT3 or FLT5.

## Outcome classification

- Outcome A: packet, factor identity, gcd branch control, away power split,
  ramified valuation shape, and route classification are complete.
- Outcome B: the primitive packet and valuation routing are complete, but exact
  gcd equality or the branch-away factor split requires a clearly identified
  follow-up.
- Outcome C: a proposed branch statement is false; report the explicit
  arithmetic obstruction and preserve the completed FLT7-005 API.

Commit with a focused message and push to the current feature branch.
