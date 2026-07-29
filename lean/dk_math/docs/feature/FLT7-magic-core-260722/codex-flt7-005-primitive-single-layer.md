# FLT7-005 — Primitive cyclotomic single-layer saturation

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Current completed checkpoint:

```text
a2fe073a Add FLT7 maximal axis depth
```

## Objective

Prove that the seventh cyclotomic magic core contains exactly one `sevenAxis`
layer when the endpoint gap is divisible by `7` but the endpoint itself is not.

The key phenomenon is saturation:

```text
7 ∣ z-y
7 ∤ y
→ sevenAxisDepth (cyclotomicSevenToTraceOne z y) = 1.
```

Thus even if `7^k ∣ z-y` for a large `k`, the primitive cyclotomic kernel does
not inherit `k` axis layers. It receives one ramified layer and leaves a
terminal non-`7` residual core.

Then specialize this to natural coprime endpoints and the existing `GN 7`
bridge, obtaining the exact valuation classification

```text
padicValNat 7 (GN 7 (a-b) b) = if 7 ∣ a-b then 1 else 0
```

under `b ≤ a` and `Nat.Coprime a b`.

Do not invoke general LTE or ideal factorization. Expose the direct degree-seven
congruence responsible for the single layer.

## New module

Create:

```text
DkMath/FLT/Seven/PrimitiveCyclotomicDepth.lean
```

Import:

```lean
import DkMath.FLT.Seven.AxisDepth
```

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenPrimitiveCyclotomicDepth.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-005.md
```

## Mathematical core

Let

```text
d = z-y.
```

Use the direct endpoint-gap expansion

```text
cyclotomicSeven (y+d) y
  = d^6 + 7*d^5*y + 21*d^4*y^2 + 35*d^3*y^3
      + 35*d^2*y^4 + 21*d*y^5 + 7*y^6.
```

When `7 ∣ d`, every term except the final `7*y^6` is divisible by `49`.
Therefore

```text
cyclotomicSeven z y ≡ 7*y^6 mod 49.
```

If `7 ∤ y`, then `49 ∤ cyclotomicSeven z y`.

This direct congruence is the heart of the checkpoint.

## Required integer theorems

Names may be adjusted minimally to local style, but preserve the mathematical
surface and report final names.

### 1. Gap-coordinate expansion

```lean
theorem cyclotomicSeven_substitution_expansion (d y : ℤ) :
    cyclotomicSeven (y + d) y =
      d ^ 6 + 7 * d ^ 5 * y + 21 * d ^ 4 * y ^ 2
        + 35 * d ^ 3 * y ^ 3 + 35 * d ^ 2 * y ^ 4
        + 21 * d * y ^ 5 + 7 * y ^ 6
```

A differently associated but definitionally equivalent polynomial expression is
acceptable.

### 2. Mod-49 residue

```lean
theorem fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow
    {z y : ℤ}
    (hgap : (7 : ℤ) ∣ z - y) :
    (49 : ℤ) ∣ cyclotomicSeven z y - 7 * y ^ 6
```

Use the divisibility witness for `z-y=7*k`, substitute `z=y+7*k`, and close by
ring arithmetic with an explicit witness for the multiple of `49` if needed.

### 3. No second layer

```lean
theorem not_fortyNine_dvd_cyclotomicSeven
    {z y : ℤ}
    (hgap : (7 : ℤ) ∣ z - y)
    (hy : ¬ (7 : ℤ) ∣ y) :
    ¬ (49 : ℤ) ∣ cyclotomicSeven z y
```

From the mod-49 residue, a hypothetical `49 ∣ cyclotomicSeven z y` gives
`49 ∣ 7*y^6`; cancel the concrete nonzero factor `7`, then use primality of `7`
to derive `7 ∣ y`, contradicting `hy`.

Do not prove this by importing a general cyclotomic LTE theorem.

### 4. Exact axis depth one

```lean
theorem sevenAxisDepth_cyclotomicSeven_eq_one
    {z y : ℤ}
    (hgap : (7 : ℤ) ∣ z - y)
    (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) = 1
```

Suggested architecture:

1. `hy` implies `y ≠ 0`, so the cyclotomic coordinate is nonzero by the existing
   coordinate zero-fiber theorem.
2. FLT7-002 gives one `sevenAxis` factor from `7 ∣ z-y`.
3. FLT7-003 converts two axis factors into `49 ∣ cyclotomicSeven z y`.
4. The no-second-layer theorem forbids this.
5. Use the FLT7-004 maximal-depth characterization to conclude depth exactly
   `1`.

### 5. Exact depth zero off the gap channel

```lean
theorem sevenAxisDepth_cyclotomicSeven_eq_zero
    {z y : ℤ}
    (hgap : ¬ (7 : ℤ) ∣ z - y)
    (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) = 0
```

Use the one-layer criterion from FLT7-002 and maximality from FLT7-004.

### 6. Full local classification

```lean
theorem sevenAxisDepth_cyclotomicSeven_eq_if
    {z y : ℤ}
    (hy : ¬ (7 : ℤ) ∣ y) :
    sevenAxisDepth (cyclotomicSevenToTraceOne z y) =
      if (7 : ℤ) ∣ z - y then 1 else 0
```

This is the stable integer API.

## Terminal single-layer residual

Prove existence of the residual core after the unique axis peel:

```lean
theorem exists_cyclotomicSeven_terminal_core
    {z y : ℤ}
    (hgap : (7 : ℤ) ∣ z - y)
    (hy : ¬ (7 : ℤ) ∣ y) :
    ∃ r : TraceOneInt (-2),
      cyclotomicSevenToTraceOne z y = sevenAxis * r ∧
      r ≠ 0 ∧
      ¬ sevenAxis ∣ r ∧
      ¬ (7 : ℤ) ∣ norm r ∧
      cyclotomicSeven z y = 7 * norm r ∧
      1 ≤ norm r
```

Prefer reusing `exists_terminal_sevenAxis_core` together with the exact depth-one
theorem. A direct one-layer witness from FLT7-002 is also acceptable if it keeps
the proof shorter.

This theorem is the exact formal form of single-layer roll saturation.

## Natural primitive endpoint bridge

For naturals, first isolate the elementary coprime fact:

```lean
theorem not_seven_dvd_right_of_coprime_of_seven_dvd_sub
    {a b : ℕ}
    (hab : b ≤ a)
    (hcop : Nat.Coprime a b)
    (hgap : 7 ∣ a - b) :
    ¬ 7 ∣ b
```

If `7 ∣ b`, then `7 ∣ a-b` and `a=(a-b)+b` give `7 ∣ a`; hence `7` divides
`Nat.gcd a b = 1`, contradiction.

Then prove the primitive exact-one result:

```lean
theorem sevenAxisDepth_cyclotomicSeven_nat_eq_one
    {a b : ℕ}
    (hab : b ≤ a)
    (hcop : Nat.Coprime a b)
    (hgap : 7 ∣ a - b) :
    sevenAxisDepth
      (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ)) = 1
```

## GN7 exact valuation classification

Required summit theorem:

```lean
theorem padicValNat_GN_seven_sub_eq_if
    {a b : ℕ}
    (hab : b ≤ a)
    (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) =
      if 7 ∣ a - b then 1 else 0
```

Use the existing `GN_seven_sub_eq_traceOneNorm_negTwo`, the depth definition,
and the integer/natural divisibility bridges already present. Do not re-expand
generic `GN` unless a small local cast identity is genuinely simpler.

Also expose the two convenient consequences:

```lean
theorem padicValNat_GN_seven_sub_le_one
    {a b : ℕ}
    (hab : b ≤ a)
    (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) ≤ 1
```

```lean
theorem padicValNat_GN_seven_sub_eq_one_iff
    {a b : ℕ}
    (hab : b ≤ a)
    (hcop : Nat.Coprime a b) :
    padicValNat 7 (GN 7 (a - b) b) = 1 ↔ 7 ∣ a - b
```

An explicit theorem `¬ 49 ∣ GN 7 (a-b) b` under the gap-divisible primitive
hypotheses is strongly recommended if it follows cleanly from the integer
result.

## Tests

The focused tests must include examples demonstrating saturation:

- `(z,y)=(8,1)`, gap `7`, depth `1`;
- `(z,y)=(50,1)`, gap `49`, still depth `1`;
- one endpoint pair with gap not divisible by `7`, depth `0`;
- a natural coprime GN example with gap `49`, valuation still `1`;
- terminal residual existence for a simple gap-divisible pair.

Avoid `native_decide`.

## Required report

Record:

- exact theorem surface;
- the direct endpoint-gap expansion;
- the mod-49 residue and cancellation route;
- why higher gap divisibility does not produce higher primitive cyclotomic
  depth;
- the terminal residual-core theorem;
- the natural coprime bridge;
- the exact GN7 valuation classification;
- recommended FLT7-006 boundary.

The recommended next boundary should be a primitive FLT7 counterexample packet
and valuation routing layer. It may consume the exact GN7 valuation bound, but
must not yet assume UFD, PID, ideals, or a complete FLT7 descent.

## Non-goals

Do not add:

- general LTE;
- ideal ramification theory;
- PID, UFD, Euclidean, or class-number arguments;
- a general prime-`p` cyclotomic theorem;
- exact valuation when both endpoints are divisible by `7`;
- equality with the valuation of `z-y` beyond the `0/1` primitive
  classification;
- an FLT7 no-solution theorem;
- a full descent;
- changes to FLT3 or FLT5.

## Outcome classification

- Outcome A: direct mod-49 residue, exact primitive depth `0/1`, terminal core,
  and GN7 valuation classification are complete.
- Outcome B: the integer single-layer theorem is complete, but the natural
  coprime/GN bridge requires a clearly identified coercion follow-up.
- Outcome C: a concrete primitive counterexample has cyclotomic depth greater
  than `1`, or the proposed residue identity is false; report the exact data and
  stop.

Commit with a focused message and push to the current feature branch.
