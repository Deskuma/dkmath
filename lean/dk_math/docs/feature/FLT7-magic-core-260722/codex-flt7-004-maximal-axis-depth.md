# FLT7-004 — Maximal seven-axis depth and terminal residual core

Work on branch:

```text
feature/FLT7-magic-core-260722-v0
```

Current completed checkpoint:

```text
98e0d08f Add FLT7 finite axis power roll
```

## Objective

Turn the finite power-roll API from FLT7-003 into a maximal finite depth for
nonzero elements of `TraceOneInt (-2)`.

Define the depth through the natural `7`-adic valuation of the positive norm,
not through an independently recursive search:

```text
sevenAxisDepth x = padicValNat 7 (Int.natAbs (norm x)).
```

The central characterization must be:

```text
x ≠ 0 → (sevenAxis ^ n ∣ x ↔ n ≤ sevenAxisDepth x).
```

Then prove that `sevenAxisDepth x` is attained, its successor is not attained,
and peeling exactly that many layers leaves a nonzero residual core whose norm
is not divisible by `7`.

This checkpoint fixes the zero convention explicitly:

```text
sevenAxisDepth 0 = 0.
```

Do not claim the divisibility characterization for zero. Every finite axis
power divides zero, whereas `padicValNat 7 0 = 0` in the current natural-valued
API. Zero is treated as absence of a nonzero core, not as an infinitely deep
roll.

## New module

Create:

```text
DkMath/FLT/Seven/AxisDepth.lean
```

Import:

```lean
import DkMath.FLT.Seven.AxisPowerRoll
```

Use an existing DkMath or Mathlib `padicValNat` bridge with the smallest sensible
import surface. `DkMath.ABC.PadicValNat.padicValNat_le_iff_dvd` is available,
but avoid an unnecessary ABC dependency if the underlying Mathlib theorem
`padicValNat_dvd_iff_le` is cleaner locally.

Update:

```text
DkMath/FLT/Seven.lean
```

Add focused tests:

```text
DkMathTest/FLT/SevenAxisDepth.lean
```

Create:

```text
docs/feature/FLT7-magic-core-260722/report-flt7-004.md
```

## Required definition

```lean
def sevenAxisDepth (x : TraceOneInt (-2)) : ℕ :=
  padicValNat 7 (Int.natAbs (norm x))
```

Add the transparent evaluation theorem if useful:

```lean
@[simp] theorem sevenAxisDepth_zero : sevenAxisDepth 0 = 0
```

Do not hide a different zero convention inside the definition.

## Required bridge lemmas

For nonzero `x`, establish the norm facts needed to move between integer and
natural divisibility:

```lean
0 < norm x
Int.natAbs (norm x) ≠ 0
```

Isolate a local theorem of the following mathematical content:

```lean
((7 : ℤ) ^ n ∣ norm x) ↔ 7 ^ n ∣ Int.natAbs (norm x)
```

The theorem may be stated for all `x` if the proof is naturally general, or for
`x ≠ 0` if positivity is the clean route. Prefer existing coercion/divisibility
APIs over manual quotient arithmetic, but a short explicit witness conversion
is acceptable.

## Summit characterization

```lean
theorem sevenAxis_pow_dvd_iff_le_sevenAxisDepth
    {x : TraceOneInt (-2)} (hx : x ≠ 0) (n : ℕ) :
    sevenAxis ^ n ∣ x ↔ n ≤ sevenAxisDepth x
```

Proof architecture:

1. use FLT7-003:

```text
sevenAxis ^ n ∣ x ↔ (7 : ℤ)^n ∣ norm x;
```

2. transfer integer divisibility to natural divisibility of
   `Int.natAbs (norm x)`;
3. use the prime-`7` theorem

```text
7^n ∣ m ↔ n ≤ padicValNat 7 m
```

with `m ≠ 0` supplied by `hx` and the positive-definite zero fiber.

## Maximality API

Prove attainment:

```lean
theorem sevenAxis_pow_depth_dvd
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    sevenAxis ^ sevenAxisDepth x ∣ x
```

Prove strict maximality:

```lean
theorem not_sevenAxis_pow_succ_depth_dvd
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    ¬ sevenAxis ^ (sevenAxisDepth x + 1) ∣ x
```

Also provide the convenient upper-bound form:

```lean
theorem le_sevenAxisDepth_of_pow_dvd
    {x : TraceOneInt (-2)} (hx : x ≠ 0) {n : ℕ}
    (hdiv : sevenAxis ^ n ∣ x) :
    n ≤ sevenAxisDepth x
```

and, if not just a one-line alias, the converse:

```lean
theorem sevenAxis_pow_dvd_of_le_depth
    {x : TraceOneInt (-2)} (hx : x ≠ 0) {n : ℕ}
    (hn : n ≤ sevenAxisDepth x) :
    sevenAxis ^ n ∣ x
```

## Depth thickness bound

Use the FLT7-003 finite-thickness theorem at the attained depth:

```lean
theorem pow_seven_depth_le_norm
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    (7 : ℤ) ^ sevenAxisDepth x ≤ norm x
```

This theorem is the finite termination witness. The natural depth cannot exceed
what the positive norm can pay for.

An additional coarse bound such as

```text
sevenAxisDepth x ≤ Int.natAbs (norm x)
```

is optional and should only be added if it follows directly from an existing
`padicValNat` bound.

## Terminal residual core

Prove existence of a residual element after peeling the maximal number of
layers:

```lean
theorem exists_terminal_sevenAxis_core
    {x : TraceOneInt (-2)} (hx : x ≠ 0) :
    ∃ y : TraceOneInt (-2),
      x = sevenAxis ^ sevenAxisDepth x * y ∧
      y ≠ 0 ∧
      ¬ sevenAxis ∣ y ∧
      ¬ (7 : ℤ) ∣ norm y ∧
      norm x = (7 : ℤ) ^ sevenAxisDepth x * norm y ∧
      1 ≤ norm y
```

Use the attained divisibility theorem to obtain the factorization witness.

- `y ≠ 0` follows from `x ≠ 0` and the explicit equality.
- If `sevenAxis ∣ y`, then reassemble one additional axis layer and contradict
  `not_sevenAxis_pow_succ_depth_dvd`.
- Convert `¬ sevenAxis ∣ y` to `¬ 7 ∣ norm y` using FLT7-002.
- Obtain exact norm scaling and the positive norm floor from existing theorems.

Do not define a canonical residual quotient in this checkpoint. Existential
output is sufficient and avoids introducing choice-dependent public data.

## Optional exact examples

Only after the required surface is complete, prove one or both:

```lean
sevenAxisDepth (sevenAxis ^ n) = n
```

```lean
sevenAxisDepth (cyclotomicSevenToTraceOne z y)
  = padicValNat 7 (Int.natAbs (cyclotomicSeven z y))
```

For the cyclotomic equality, use the existing norm identity. Do not yet derive
an exact endpoint-gap valuation formula.

## Tests

The focused test must cover:

- `sevenAxisDepth 0 = 0`;
- a unit or another norm-one element has depth `0`;
- `sevenAxis` has depth `1` if the optional exact example is proved;
- `sevenAxis^2` has depth `2` if the optional exact example is proved;
- characterization at `n = 0`, `n = depth`, and `n = depth + 1`;
- terminal residual existence for a simple explicit axis multiple.

Avoid `native_decide`.

## Required report

Record:

- exact definition and zero convention;
- integer-to-natural norm divisibility bridge;
- the maximality characterization;
- attainment and successor obstruction;
- the finite termination/thickness witness;
- terminal residual-core construction;
- optional examples included or omitted;
- recommended FLT7-005 boundary.

The recommended next boundary should investigate the exact depth of the seventh
cyclotomic kernel under primitive endpoint hypotheses. In particular, do not
assume in this checkpoint that higher divisibility of `z-y` produces the same
higher depth in `cyclotomicSeven z y`.

## Non-goals

Do not add:

- a recursive search definition of depth;
- an infinite-valued valuation type;
- a divisibility characterization for zero;
- canonical quotient data chosen by `Classical.choose` as a public definition;
- LTE for the seventh cyclotomic kernel;
- exact comparison with `padicValNat 7 (Int.natAbs (z-y))`;
- coprime or primitive endpoint packets;
- FLT7 descent or a no-solution theorem;
- ideal, PID, UFD, Euclidean, or class-number theory;
- general odd-prime abstractions.

## Outcome classification

- Outcome A: depth definition, nonzero divisibility characterization,
  maximality, thickness bound, and terminal residual core are complete.
- Outcome B: maximality and depth characterization are complete, but the
  residual-core package or an integer/natural coercion theorem requires a
  clearly identified follow-up.
- Outcome C: the proposed valuation characterization conflicts with the
  existing zero convention or divisibility API; report the precise blocker and
  preserve the completed finite power-roll API.

Commit with a focused message and push to the current feature branch.
