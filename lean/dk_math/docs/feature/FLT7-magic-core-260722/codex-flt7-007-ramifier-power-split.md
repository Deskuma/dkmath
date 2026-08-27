# FLT7-007 — Exact ramifier stripping and quadratic residual packet

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Current completed checkpoint:

```text
FLT7-006 local commit/push — primitive counterexample valuation routing
```

Use the actual current branch HEAD as the implementation base.

## Objective

Consume the ramified `SevenAdicCounterexamplePacket` from FLT7-006 and remove
the exact common factor `7` from the gap/residual pair.

The natural arithmetic summit is the exact normal form

```text
z-y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
x = 7 * a * b
```

with positive coprime `a,b` and `7 ∤ b`.

Then connect the power split to the quadratic magic core.  After the unique
`sevenAxis` layer is removed from

```text
cyclotomicSevenToTraceOne z y,
```

the terminal residual element must have norm exactly `b^7`.

This checkpoint must stop at the residual norm packet.  Do not assert that the
residual element itself is a seventh power in `TraceOneInt (-2)`.

## New modules

Create:

```text
DkMath/FLT/Seven/SevenAdicPowerSplit.lean
DkMath/FLT/Seven/QuadraticResidualPacket.lean
```

Suggested imports:

```lean
-- SevenAdicPowerSplit.lean
import DkMath.FLT.Seven.CounterexampleRouting

-- QuadraticResidualPacket.lean
import DkMath.FLT.Seven.SevenAdicPowerSplit
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenAdicPowerSplit.lean
DkMathTest/FLT/SevenQuadraticResidualPacket.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-007.md
```

## Part A — Stripped natural cores

For a ramified packet `p : SevenAdicCounterexamplePacket x y z`, introduce the
local stripped quantities in the construction proof:

```text
c := (z-y) / 7
r := GN 7 (z-y) y / 7
d := x / 7
```

Use the packet fields to prove exact reconstruction:

```text
z-y = 7*c
GN 7 (z-y) y = 7*r
x = 7*d.
```

The residual reconstruction should use `p.residual_padicValNat = 1` to obtain
`7 ∣ GN 7 (z-y) y` if that divisibility is not already directly available.

Prove:

```lean
theorem sevenAdicPacket_residual_not_fortyNine_dvd
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 49 ∣ GN 7 (z - y) y
```

and equivalently for the stripped residual:

```lean
theorem sevenAdicPacket_seven_not_dvd_strippedResidual
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    ¬ 7 ∣ GN 7 (z - y) y / 7
```

Use the exact valuation-one field or FLT7-005's no-`49` theorem. Avoid a new
mod-49 expansion.

## Part B — Coprimality after removing the common ramifier

From

```text
gcd(z-y, GN 7 (z-y) y) = 7
```

prove the stripped cores are coprime:

```lean
theorem sevenAdicPacket_coprime_div_seven
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime
      ((z - y) / 7)
      ((GN 7 (z - y) y) / 7)
```

Prefer `Nat.coprime_div_gcd_div_gcd` after rewriting the packet gcd to `7`.

Then strengthen by placing the missing ramifier load on the gap side:

```lean
theorem sevenAdicPacket_coprime_scaledGap_residual
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    Nat.Coprime
      (7 ^ 2 * ((z - y) / 7))
      ((GN 7 (z - y) y) / 7)
```

The factor `7^2` is coprime to the stripped residual because the latter is not
divisible by `7`.

## Part C — Normalized seventh-power product

Prove the exact normalized product identity:

```lean
theorem sevenAdicPacket_normalized_product
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    (7 ^ 2 * ((z - y) / 7)) *
        ((GN 7 (z - y) y) / 7) =
      (7 * (x / 7)) ^ 7
```

This is the exponent-seven analogue of the established FLT5 ramifier stripping
pattern.

Mathematically:

```text
(z-y)=7c,
GN=7r,
x=7d,
(7c)(7r)=(7d)^7
→ (7^2 c)r=(7d)^7.
```

Do not cancel powers by informal arithmetic; prove the reconstruction
identities and close the normalization by rewriting and `ring`/`ring_nf`.

## Part D — Exact seventh-power split

Define:

```lean
structure SevenAdicPowerSplit (x y z : ℕ) : Type where
  sevenAdic : SevenAdicCounterexamplePacket x y z
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  gap_eq : z - y = 7 ^ 6 * a ^ 7
  residual_eq : GN 7 (z - y) y = 7 * b ^ 7
  distinguished_eq : x = 7 * a * b
```

Required theorem:

```lean
theorem SevenAdicPowerSplit.seven_not_dvd_b
    {x y z : ℕ}
    (s : SevenAdicPowerSplit x y z) :
    ¬ 7 ∣ s.b
```

Use `residual_eq` and the exact residual valuation one/no-`49` property.

Prove existence from every ramified packet:

```lean
theorem nonempty_sevenAdicPowerSplit_of_packet
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    Nonempty (SevenAdicPowerSplit x y z)
```

Recommended construction architecture:

1. set

```text
c=(z-y)/7,
r=GN/7,
d=x/7;
```

2. prove `Coprime (7^2*c) r`;
3. use the normalized product and `seventh_power_factor_split` to obtain

```text
7^2*c = A^7,
r = b^7;
```

4. derive `7 ∣ A` from `7^2 ∣ A^7` and primality of `7`;
5. write `A=7*a`;
6. cancel the positive factor `7^2` to derive

```text
c=7^5*a^7;
```

7. reconstruct

```text
z-y=7^6*a^7,
GN=7*b^7;
```

8. prove `x=7*a*b` by injectivity of the seventh-power map on naturals after
   comparing seventh powers;
9. recover positivity and `Coprime a b` from the stripped-core coprimality.

Use the FLT5 power-split proof only as an architectural reference; do not import
any FLT5 module.

Expose a chosen split for downstream work:

```lean
noncomputable def sevenAdicPowerSplit_of_packet
    {x y z : ℕ}
    (p : SevenAdicCounterexamplePacket x y z) :
    SevenAdicPowerSplit x y z :=
  Classical.choice (nonempty_sevenAdicPowerSplit_of_packet p)
```

Also provide a direct constructor from a counterexample and ramified branch:

```lean
noncomputable def sevenAdicPowerSplit_of_counterexample
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z-y) :
    SevenAdicPowerSplit x y z
```

## Part E — Quadratic terminal residual packet

The FLT7-005 theorem

```text
exists_cyclotomicSeven_terminal_core
```

provides a terminal element after removing the unique `sevenAxis` layer.
Package this together with the exact natural power split.

Define:

```lean
structure SevenQuadraticResidualPacket (x y z : ℕ) : Type where
  powerSplit : SevenAdicPowerSplit x y z
  residualCore : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) =
      sevenAxis * residualCore
  residual_ne_zero : residualCore ≠ 0
  residual_terminal : ¬ sevenAxis ∣ residualCore
  residual_norm_not_seven_dvd : ¬ (7 : ℤ) ∣ norm residualCore
  residual_norm_eq :
    norm residualCore = (powerSplit.b : ℤ) ^ 7
  residual_norm_pos : 1 ≤ norm residualCore
```

Prove:

```lean
theorem nonempty_sevenQuadraticResidualPacket_of_powerSplit
    {x y z : ℕ}
    (s : SevenAdicPowerSplit x y z) :
    Nonempty (SevenQuadraticResidualPacket x y z)
```

Suggested route:

1. extract `hPack` and `7∣z-y` from `s.sevenAdic`;
2. obtain `7∤y` from the ramified packet;
3. specialize `exists_cyclotomicSeven_terminal_core` to integer endpoints
   `(z,y)`;
4. use the existing equality between `cyclotomicSeven z y` and
   `GN 7 (z-y) y`, together with

```text
GN 7 (z-y) y = 7*b^7,
cyclotomicSeven z y = 7*norm residualCore,
```

5. cancel the nonzero integer factor `7` to conclude

```text
norm residualCore = b^7.
```

Keep all casts explicit and localized. Add a small bridge theorem if the
existing GN/cyclotomic equality is awkward to rewrite.

Expose chosen downstream data:

```lean
noncomputable def sevenQuadraticResidualPacket_of_powerSplit
    {x y z : ℕ}
    (s : SevenAdicPowerSplit x y z) :
    SevenQuadraticResidualPacket x y z
```

and a direct constructor from a ramified branch if concise.

## Useful consequences

Prove at least:

```lean
theorem SevenQuadraticResidualPacket.norm_is_seventh_power
    {x y z : ℕ}
    (q : SevenQuadraticResidualPacket x y z) :
    ∃ b : ℕ, norm q.residualCore = (b : ℤ) ^ 7
```

```lean
theorem SevenQuadraticResidualPacket.norm_positive
    {x y z : ℕ}
    (q : SevenQuadraticResidualPacket x y z) :
    0 < norm q.residualCore
```

Do not prove or state that `residualCore` itself is a unit times a seventh power.
That is the next algebraic boundary.

## Tests

The focused tests should exercise abstract wiring only:

- reconstruction of stripped cores from an abstract ramified packet;
- coprimality after removing `7`;
- normalized product identity;
- extraction of `gap_eq`, `residual_eq`, and `distinguished_eq` from a chosen
  `SevenAdicPowerSplit`;
- `7 ∤ b`;
- construction of a quadratic residual packet;
- extraction of terminality and seventh-power norm.

Do not instantiate a real counterexample.
Avoid `native_decide`.

## Required report

Record:

- exact theorem and structure surface;
- stripped reconstruction identities;
- coprimality after dividing by the common gcd `7`;
- normalized product architecture;
- derivation of

```text
z-y=7^6*a^7,
GN=7*b^7,
x=7ab;
```

- positivity, coprimality, and `7∤b`;
- quadratic terminal residual construction;
- exact proof that its norm is `b^7`;
- recommended FLT7-008 boundary.

The recommended next boundary should investigate the arithmetic of
`TraceOneInt (-2)` needed to turn a terminal element of seventh-power norm into
an element-level seventh-power normal form. Separate the following possible
routes clearly:

1. direct Euclidean-domain structure for the discriminant `-7` order;
2. direct coprime-conjugate factor extraction without a global UFD instance;
3. finite unit classes modulo seventh powers.

Do not start a descent until the element-level factorization and unit-sector
surface are explicit.

## Non-goals

Do not add:

- an FLT7 contradiction or no-solution theorem;
- a complete descent;
- a claim that the quadratic residual is already a seventh power;
- a Euclidean/PID/UFD instance;
- ideal or class-number theory;
- finite unit-class classification;
- general LTE;
- a general prime-exponent abstraction;
- changes to FLT3 or FLT5.

## Outcome classification

- Outcome A: exact ramifier power split and quadratic residual packet with norm
  `b^7` are complete.
- Outcome B: natural power split is complete, but the quadratic residual bridge
  requires a clearly identified cast or coordinate follow-up.
- Outcome C: the proposed normalization or exact exponents are false; report
  the precise arithmetic obstruction and preserve FLT7-006.

Commit with a focused message and push to the current feature branch.
