# Codex instruction: FLT7-001 magic-core foundation

## 0. Repository and branch

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
feature/FLT7-magic-core-260722-v0
```

Base feature:

```text
feature/FLT35-essence-260722-v0
```

Read first:

```text
README.md
AGENT.md
SUMMARY.md
lean/dk_math/docs/feature/FLT35-essence-260722/README.md
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
lean/dk_math/DkMath/FLT/ThreeTraceOneBridge.lean
lean/dk_math/DkMath/FLT/Five/TraceOneBridge.lean
lean/dk_math/DkMath/FLT/QuadraticEssence.lean
```

Use current GitHub source as the implementation truth. Do not reopen or edit the completed FLT3 / FLT5 feature except for imports required by this new feature.

## 1. Goal

Create the first Lean-realized FLT7 magic-core layer.

This checkpoint does not prove FLT7.

It must establish three exact structures:

```text
1. the trace-one parameter s = -2 has a central seven-axis kappa with kappa^2 = -7;
2. its norm is positive definite and has nonzero floor 1;
3. the homogeneous seventh cyclotomic kernel is exactly that norm in explicit cubic coordinates.
```

Mathematical target:

```text
GN7 / Phi7 -> TraceOneInt (-2) norm
```

The feature interpretation is:

```text
seven-degree outward growth
  -> two cubic coordinates
  -> quadratic positive-definite norm
  -> zero is possible only for the zero element
  -> every nonzero integral core has norm at least 1
```

## 2. Mathematical definitions

Work in:

```lean
DkMath.NumberTheory.TraceOneQuadratic
```

with:

```lean
TraceOneInt (-2)
```

Define the central seven-axis:

```lean
def sevenAxis : TraceOneInt (-2) :=
  2 * tau (-2) - 1
```

The intended coordinates are:

```text
sevenAxis = (-1, 2)
```

Its exact identities are:

```text
sevenAxis^2 = -7
conj sevenAxis = -sevenAxis
norm sevenAxis = 7
```

Do not call `sevenAxis` a ring unit. Its norm is `7`, not `±1`.

## 3. Positive-definite norm at s = -2

Add the specialization:

```lean
theorem traceOneNorm_neg_two (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) =
      a ^ 2 + a * b + 2 * b ^ 2
```

Add the completed-square identity:

```lean
theorem four_mul_traceOneNorm_negTwo_eq_sum_sq (a b : ℤ) :
    4 * norm (⟨a, b⟩ : TraceOneInt (-2)) =
      (2 * a + b) ^ 2 + 7 * b ^ 2
```

Then prove the zero-floor theorem:

```lean
theorem traceOneNorm_negTwo_eq_zero_iff (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) = 0 ↔ a = 0 ∧ b = 0
```

Also prove the structured form:

```lean
theorem norm_eq_zero_iff_of_negTwo (x : TraceOneInt (-2)) :
    norm x = 0 ↔ x = 0
```

Then prove the nonzero integral floor:

```lean
theorem one_le_traceOneNorm_negTwo_of_ne_zero
    (x : TraceOneInt (-2)) (hx : x ≠ 0) :
    1 ≤ norm x
```

Because the codomain is `ℤ`, use the exact integer order statement. Do not move to `Nat` unless a clean bridge is needed.

Finally classify norm one:

```lean
theorem traceOneNorm_negTwo_eq_one_iff (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-2)) = 1 ↔
      (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)
```

and, if clean:

```lean
theorem norm_eq_one_iff_of_negTwo (x : TraceOneInt (-2)) :
    norm x = 1 ↔ x = 1 ∨ x = -1
```

These theorems are the formal version of:

```text
zero is not the next inner shell;
zero is the absence of the core;
one is the smallest nonzero integral norm shell.
```

## 4. Seventh cyclotomic kernel

Create:

```text
DkMath/FLT/Seven/QuadraticBridge.lean
```

Namespace:

```lean
namespace DkMath.FLT.Seven
```

Define the homogeneous seventh cyclotomic kernel over integers:

```lean
def cyclotomicSeven (z y : ℤ) : ℤ :=
  z ^ 6 + z ^ 5 * y + z ^ 4 * y ^ 2 + z ^ 3 * y ^ 3
    + z ^ 2 * y ^ 4 + z * y ^ 5 + y ^ 6
```

Define the explicit cubic coordinates:

```lean
def cyclotomicSevenFst (z y : ℤ) : ℤ :=
  z ^ 3 + z ^ 2 * y - y ^ 3

def cyclotomicSevenSnd (z y : ℤ) : ℤ :=
  -z ^ 2 * y - z * y ^ 2
```

Define the trace-one coordinate package:

```lean
def cyclotomicSevenToTraceOne (z y : ℤ) : TraceOneInt (-2) :=
  ⟨cyclotomicSevenFst z y, cyclotomicSevenSnd z y⟩
```

Prove the central identity:

```lean
theorem cyclotomicSeven_eq_traceOneNorm_negTwo (z y : ℤ) :
    cyclotomicSeven z y =
      norm (cyclotomicSevenToTraceOne z y)
```

This should be a transparent polynomial proof using `simp` and `ring`.

Do not use `native_decide`.

## 5. Difference-of-seventh-powers bridge

Prove the standard factorization directly or reuse an existing `GN` theorem if the import boundary remains thin:

```lean
theorem seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven (z y : ℤ) :
    z ^ 7 - y ^ 7 = (z - y) * cyclotomicSeven z y
```

Then provide a `GN 7` bridge only if the existing generic `GN` API makes the statement natural and stable.

Preferred theorem shape for natural inputs:

```lean
theorem GN_seven_sub_eq_traceOneNorm_negTwo
    (a b : ℕ) (hab : b ≤ a) :
    ((GN 7 (a - b) b : ℕ) : ℤ) =
      norm
        (cyclotomicSevenToTraceOne (a : ℤ) (b : ℤ))
```

However, verify the actual coordinate convention carefully.

The homogeneous factor is:

```text
Phi7(z,y) = (z^7 - y^7)/(z-y)
```

while `GN 7 g y` usually uses `z = g + y`.

Therefore the correct bridge may require:

```text
cyclotomicSevenToTraceOne ((g + y : ℕ) : ℤ) (y : ℤ)
```

Do not force the theorem statement before checking the existing `GN` convention.

The report must record the exact coordinate substitution used.

## 6. Zero-fiber theorems

First prove the coordinate fiber theorem:

```lean
theorem cyclotomicSeven_coordinates_eq_zero_iff (z y : ℤ) :
    cyclotomicSevenFst z y = 0 ∧ cyclotomicSevenSnd z y = 0 ↔
      z = 0 ∧ y = 0
```

A direct proof may use the factorization:

```text
cyclotomicSevenSnd z y = -z*y*(z+y)
```

and case analysis.

Then prove:

```lean
theorem cyclotomicSeven_eq_zero_iff (z y : ℤ) :
    cyclotomicSeven z y = 0 ↔ z = 0 ∧ y = 0
```

Prefer deriving this through the norm zero theorem and the coordinate theorem rather than reproving positivity from scratch.

If the coordinate theorem becomes disproportionately awkward in this checkpoint, use the alternative direct positive-definite route for `cyclotomicSeven_eq_zero_iff`, and report the coordinate theorem as deferred. Do not introduce a large algebraic dependency solely for it.

## 7. Positive natural chamber

For positive naturals, prove a minimal lower bound if it is clean:

```lean
theorem seven_le_cyclotomicSeven_nat
    (z y : ℕ) (hz : 0 < z) (hy : 0 < y) :
    7 ≤
      z ^ 6 + z ^ 5 * y + z ^ 4 * y ^ 2 + z ^ 3 * y ^ 3
        + z ^ 2 * y ^ 4 + z * y ^ 5 + y ^ 6
```

This is optional for Outcome A. It is useful because it separates:

```text
integral nonzero norm floor = 1
positive FLT chamber floor = 7
```

Do not spend excessive proof effort here.

## 8. File layout

Required files:

```text
DkMath/NumberTheory/TraceOneQuadratic.lean
DkMath/FLT/Seven/QuadraticBridge.lean
DkMath/FLT/Seven.lean
DkMathTest/FLT/SevenQuadraticBridge.lean
docs/feature/FLT7-magic-core-260722/README.md
docs/feature/FLT7-magic-core-260722/report-flt7-001.md
```

Update aggregators only as needed:

```text
DkMath/FLT.lean
```

Do not import FLT3 or FLT5 proof towers into FLT7.

Allowed dependency direction:

```text
TraceOneQuadratic
      ↓
Seven.QuadraticBridge
      ↓
Seven facade / FLT aggregator
```

## 9. Test and axiom audit

The test file must include examples and `#print axioms` for at least:

```text
traceOne_tau_sq
traceOne_norm_mul
sevenAxis_sq
sevenAxis_norm
traceOneNorm_negTwo_eq_zero_iff
one_le_traceOneNorm_negTwo_of_ne_zero
traceOneNorm_negTwo_eq_one_iff
cyclotomicSeven_eq_traceOneNorm_negTwo
cyclotomicSeven_eq_zero_iff
```

Reject:

```text
sorryAx
DkMath-defined axioms
native_decide
admit
sorry
```

Standard Lean axioms such as `propext`, `Classical.choice`, and `Quot.sound` may appear; record the exact sets rather than calling the results axiom-free.

## 10. README structure

The feature README must document:

1. status: implementation checkpoint;
2. the magic-core interpretation;
3. exact distinction between ring unit and scale axis;
4. `sevenAxis^2 = -7`, conjugation, and norm `7`;
5. positive-definite norm and zero floor;
6. norm-one classification;
7. seventh cyclotomic cubic-coordinate identity;
8. GN coordinate substitution;
9. exact theorem surface;
10. explicit non-goals.

Use the following terminology carefully:

```text
sevenAxis / kappa:
  central quadratic scale axis
  not a ring unit

zero:
  zero element only
  not an inner norm shell

one:
  smallest nonzero integral norm shell
```

## 11. Strict non-goals

Do not:

- prove FLT7;
- define a full seventh-power counterexample packet;
- build a Euclidean domain, PID, UFD, or class-number-one instance for `TraceOneInt (-2)`;
- classify all irreducibles or primes;
- implement seventh-power unit sectors;
- implement descent;
- add a general odd-prime theorem;
- claim `sevenAxis` is a unit;
- generalize the positive-definite theorem to all `p ≡ 3 mod 4` in this checkpoint;
- modify FLT3 or FLT5 theorem statements;
- create a standalone FLT7 proof artifact.

## 12. Verification

Run:

```bash
cd lean/dk_math

lake build DkMath.NumberTheory.TraceOneQuadratic
lake build DkMath.FLT.Seven.QuadraticBridge
lake build DkMath.FLT.Seven
lake env lean DkMathTest/FLT/SevenQuadraticBridge.lean

grep -RIn --include='*.lean' \
  -E '\bnative_decide\b|\badmit\b|\bsorry\b' \
  DkMath/FLT/Seven DkMathTest/FLT/SevenQuadraticBridge.lean

git diff --check
```

Treat the supplied checkpoint as Lean-accepted if all target builds pass.

## 13. Outcomes

### Outcome A

All required magic-core, positive-definite, cyclotomic bridge, zero-fiber, tests, and documentation are complete.

### Outcome B

The central norm identity and zero floor are complete, but one optional theorem or direct coordinate-fiber theorem is deferred with a precise reason.

### Outcome C

The proposed seventh cyclotomic coordinates do not match the `s = -2` norm, the GN substitution is inconsistent, or another material mathematical contradiction is found. Stop and report the exact contradiction.

## 14. Report requirements

Create `report-flt7-001.md` containing:

- Outcome A, B, or C;
- files changed;
- exact theorem and definition names;
- seven-axis coordinates;
- proof of `sevenAxis^2 = -7` meaning;
- exact norm-zero and norm-one results;
- seventh cyclotomic coordinate identity;
- exact GN substitution;
- optional natural lower-bound status;
- axiom audit;
- non-goals preserved;
- recommended next checkpoint.

Recommended next checkpoint if Outcome A or B:

```text
FLT7-002: seven-axis divisibility and the relation between kappa-depth and 7-adic norm depth
```

## 15. Commit boundary

One implementation commit is preferred.

Suggested commit message:

```text
Add FLT7 quadratic magic core
```

Push to:

```text
feature/FLT7-magic-core-260722-v0
```
