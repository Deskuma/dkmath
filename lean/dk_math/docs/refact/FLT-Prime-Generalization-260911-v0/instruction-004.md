# FLT prime-generalization Phase 4 — TraceOne discriminant axis and quadratic cyclotomic bridge probe

## Goal

Phase 3 established that the FLT7 ramified adic front half is a specialization of the generic odd-prime `PrimeAdicPowerSplit` kernel. The immediate downstream Seven layer enters `TraceOneInt (-2)` and discriminant `-7` arithmetic.

This phase must determine whether that boundary is genuinely `p = 7`, or whether a larger **prime-discriminant TraceOne layer** exists before the truly prime-specific algebra begins.

Do not attempt a general FLT theorem. Do not generalize the full cyclotomic field. Do not modify the proved FLT3/FLT5/FLT7 endpoints in this phase.

The bounded objectives are:

1. extract the arithmetic of the element `2*tau - 1` from the Seven-specific axis modules into a generic `TraceOneInt s` discriminant-axis API;
2. prove compatibility with the existing `p = 7`, `s = -2` axis machinery;
3. record the already-proved FLT3/FLT5/FLT7 quadratic bridge pattern at `s = -1, 1, -2`;
4. run new explicit Lean probes at `p = 11` and `p = 13` to test whether the prime cyclotomic shell again becomes a `TraceOneInt s` norm;
5. inspect local Mathlib support for quadratic characters / Gauss sums and report the precise missing bridge from the finite explicit probes to arbitrary odd prime `p`.

## Mathematical target

`TraceOneInt s` satisfies

```text
tau^2 = tau + s
Delta_s = 1 + 4*s
N_s(a,b) = a^2 + a*b - s*b^2
```

Define the neutral discriminant axis

```text
delta_s := 2*tau_s - 1
```

Expected identities:

```text
delta_s = (-1, 2)
delta_s^2 = Delta_s
conj(delta_s) = -delta_s
N_s(delta_s) = -Delta_s
```

The key generic divisibility statement to test is

```text
delta_s ∣ x  ↔  Delta_s ∣ trace(x)
```

with integer divisibility. For a prime absolute discriminant

```text
p = natAbs(Delta_s),  Nat.Prime p,
```

test the stronger equivalence

```text
delta_s ∣ x  ↔  p ∣ natAbs(N_s(x)).
```

Prefer `Int.natAbs` on norms in the generic API. The `s = 1` / discriminant `+5` norm is indefinite, so generic theorems must not silently assume positivity of the integer norm.

## Part A — generic discriminant-axis module

Create a neutral production module, preferably

```text
DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
```

importing only the neutral TraceOne layer and generic valuation support actually needed.

Recommended namespace:

```lean
namespace DkMath.NumberTheory.TraceOneQuadratic
```

Add a definition such as

```lean
def discrAxis (s : ℤ) : TraceOneInt s := 2 * tau s - 1
```

and prove, with names adjusted to project conventions if necessary:

```lean
@[simp] theorem discrAxis_eq ...
theorem discrAxis_sq ...
theorem conj_discrAxis ...
theorem norm_discrAxis ...
theorem trace_discrAxis_mul ...
theorem discrAxis_dvd_iff_discr_dvd_trace ...
```

The intended formulas are

```text
discrAxis s = ⟨-1, 2⟩
(discrAxis s)^2 = ofInt s (discr s)
conj (discrAxis s) = -discrAxis s
norm (discrAxis s) = -(discr s)
trace (discrAxis s * ⟨c,d⟩) = discr s * d
```

For the converse direction of `discrAxis_dvd_iff_discr_dvd_trace`, avoid division by two if possible. If

```text
trace ⟨a,b⟩ = discr s * k,
```

a candidate witness is

```text
⟨2*s*k - a, k⟩.
```

Verify this algebraically in Lean rather than trusting the note.

### Prime absolute-discriminant packet

Introduce only as much structure as useful. A small proposition/structure is acceptable, e.g.

```lean
PrimeDiscriminantPacket p s
```

containing at minimum

```text
Nat.Prime p
Int.natAbs (discr s) = p
```

Do not encode consequences as fields when they can be proved.

Under this contract, attempt:

```text
(p : ℤ) ∣ norm x  ↔  (p : ℤ) ∣ trace x

discrAxis s ∣ x  ↔  p ∣ Int.natAbs (norm x)
```

Use the existing identity

```text
4 * norm x = trace x ^ 2 - discr s * x.snd ^ 2
```

and primality. Be careful with the sign of `discr s`.

## Part B — generic finite axis powers and depth

Generalize only the sign-safe part of the current Seven `AxisPowerRoll` / `AxisDepth` story.

Define a depth based on absolute norm, for example

```lean
def discrAxisDepth (p : ℕ) (x : TraceOneInt s) : ℕ :=
  padicValNat p (Int.natAbs (norm x))
```

or an equivalent API that makes the `s` parameter inferable.

Under `PrimeDiscriminantPacket p s`, prove as much of the following as Lean accepts:

```text
natAbs (norm ((discrAxis s)^n)) = p^n

(discrAxis s)^n ∣ x
  ↔ p^n ∣ natAbs(norm x)
```

and, when `norm x ≠ 0`,

```text
(discrAxis s)^n ∣ x
  ↔ n ≤ discrAxisDepth p x.
```

Then attempt a generic terminal peel:

```text
∃ y,
  x = (discrAxis s)^(discrAxisDepth p x) * y
  ∧ norm y ≠ 0
  ∧ ¬ discrAxis s ∣ y
  ∧ ¬ p ∣ Int.natAbs (norm y)
  ∧ Int.natAbs (norm x)
      = p^(discrAxisDepth p x) * Int.natAbs (norm y)
  ∧ 1 ≤ Int.natAbs (norm y)
```

It is acceptable for this theorem to assume `norm x ≠ 0` rather than proving a general anisotropy theorem for every prime discriminant in this phase.

Do **not** import Seven modules into this generic production module.

## Part C — `p = 7` compatibility probe

Create a test module such as

```text
DkMathTest/FLT/Prime/TraceOneDiscriminantAxisCompatibility.lean
```

which may import the generic module and the existing Seven axis modules.

Verify at least:

```text
discr (-2) = -7
Int.natAbs (discr (-2)) = 7
discrAxis (-2) = sevenAxis
```

and show that the new generic divisibility/power/depth statements recover the existing Seven shape.

In particular compare the generic depth with

```lean
DkMath.FLT.Seven.sevenAxisDepth
```

and, where straightforward, prove equality of the two depth functions at `s = -2`, `p = 7`.

Do not delete the Seven wrappers in this phase. This is a compatibility probe first; migration can be a separate phase if GREEN.

## Part D — FLT3 / FLT5 / FLT7 quadratic-family audit

Record and compile the concrete discriminants:

```text
p = 3: s = -1, discr = -3
p = 5: s =  1, discr =  5
p = 7: s = -2, discr = -7
```

Confirm the existing bridge surface rather than re-proving the FLT endpoints:

```text
GN3 / S0  -> norm on TraceOneInt (-1)
GN5       -> norm on TraceOneInt 1
GN7       -> norm on TraceOneInt (-2)
```

Use the existing modules:

```text
DkMath.FLT.ThreeTraceOneBridge
DkMath.FLT.Five.TraceOneBridge
DkMath.FLT.Seven.QuadraticBridge
```

Classify this as a proved three-sample family, not yet an arbitrary-prime theorem.

## Part E — new explicit p=11 and p=13 Lean probes

Create a scratch/test module, e.g.

```text
DkMathTest/FLT/Prime/QuadraticCyclotomicBridgeProbe.lean
```

Do not promote the following coordinate formulas to production unless a clear reusable abstraction emerges.

### p = 11

Use `s = -3`, so

```text
discr(-3) = -11
N_{-3}(A,B) = A^2 + A*B + 3*B^2.
```

For integer endpoints `z,y`, test the homogeneous degree-five coordinates

```text
A11(z,y) = z^5 - z^3*y^2 + z^2*y^3 - z*y^4 - y^5
B11(z,y) = z^4*y + z*y^4
```

and prove by Lean normalization that

```text
A11^2 + A11*B11 + 3*B11^2
  = z^10 + z^9*y + z^8*y^2 + ... + z*y^9 + y^10.
```

Equivalently package `⟨A11,B11⟩ : TraceOneInt (-3)` and prove its norm equals the homogeneous prime-11 cyclotomic shell.

Prefer reusing `GTailCyclotomicShell 11 (z-y) y` if this avoids introducing a redundant cyclotomic definition; since `(z-y)+y=z` over `ℤ`, make the endpoint correspondence explicit.

### p = 13

Use `s = 3`, so

```text
discr(3) = 13
N_3(A,B) = A^2 + A*B - 3*B^2.
```

Test the homogeneous degree-six coordinates

```text
A13(z,y) = z^6 + 2*z^4*y^2 - z^3*y^3 + 2*z^2*y^4 + y^6
B13(z,y) = z^5*y + z^3*y^3 + z*y^5
```

and prove

```text
A13^2 + A13*B13 - 3*B13^2
  = z^12 + z^11*y + z^10*y^2 + ... + z*y^11 + y^12.
```

Again, a `TraceOneInt 3` norm formulation is preferred.

These formulas are probe inputs supplied by the design. Lean must verify them. If either identity fails, report `PGEN-FALSE` and preserve the failing statement/source; do not repair it silently by inventing a different formula.

### Why both 11 and 13 matter

They test both discriminant signs beyond the already formalized exponents:

```text
11 ≡ 3 mod 4 -> discriminant -11 -> positive-definite quadratic norm
13 ≡ 1 mod 4 -> discriminant +13 -> indefinite quadratic norm
```

If both compile, classify the result as evidence for a prime-discriminant quadratic cyclotomic pattern, **not** as proof for all primes.

## Part F — arbitrary-prime bridge audit

Inspect the pinned Mathlib tree for reusable APIs around:

```text
Mathlib.NumberTheory.GaussSum
Mathlib.NumberTheory.LegendreSymbol
Mathlib cyclotomic polynomial / cyclotomic extension APIs
quadratic characters on ZMod p
```

Report concrete declaration names that appear relevant.

The mathematical pattern to assess is the index-two / quadratic-residue split of the prime cyclotomic shell. For an odd prime `p`, the quadratic residues and non-residues partition the nonzero residue classes; the associated Gaussian-period construction should lead to the quadratic discriminant

```text
D_p = (-1)^((p-1)/2) * p.
```

Do not claim this construction has been formalized merely because Gauss-sum lemmas exist. State exactly which bridge is present in Mathlib and which polynomial/integral-coordinate theorem is still missing.

The desired future theorem shape is conceptually:

```text
∃ s : ℤ, Int.natAbs (discr s) = p ∧
  ∃ coord : ℤ → ℤ → TraceOneInt s,
    norm (coord z y) = primeCyclotomicShell p z y
```

with the correct sign/discriminant condition. This is a roadmap target only unless Phase 4 unexpectedly makes it easy.

## Classification

Use these labels in `report-004.md`:

- `PGEN-CORE-GREEN`: generic TraceOne discriminant-axis theorem compiled.
- `PGEN-COMPAT`: existing 3/5/7 or Seven API recovered as specialization.
- `PGEN-SAMPLE-GREEN`: explicit 11 or 13 cyclotomic norm identity compiled.
- `PGEN-BOUNDARY`: theorem works only under an explicit discriminant/sign/nonzero condition.
- `PGEN-MISSING-BRIDGE`: the arbitrary-prime Gaussian-period -> integral TraceOne coordinate theorem is not available.
- `PGEN-FALSE`: proposed statement is mathematically false, with a Lean/counterexample witness.

## Required verification

At minimum run focused builds for:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.FLT.Seven.QuadraticResidualPacket
lake build DkMath.FLT.Seven
```

If module names differ, record exact commands.

Add `#print axioms` checks for the main generic axis theorem(s), terminal peel if obtained, the Seven compatibility theorem, and both `p=11`, `p=13` norm identities.

No `sorry`, no new `axiom`, no `sorryAx`.

Run `git diff --check`.

## Report

Create

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-004.md
```

The report must explicitly answer:

1. How much of `AxisDivisibility`, `AxisPowerRoll`, and `AxisDepth` is actually `TraceOneInt s` generic?
2. Do the existing FLT3/FLT5/FLT7 bridges fit the signed-prime-discriminant sequence `-3,+5,-7`?
3. Do the supplied `p=11` / `p=13` coordinates pass Lean and extend the sequence to `-11,+13`?
4. What exact assumption is needed to make the generic axis-depth theory sign-safe?
5. What is the first theorem still missing for arbitrary prime `p`?
6. Based on Lean evidence, should the next phase migrate Seven axis machinery to the generic core, or attack the arbitrary-prime quadratic cyclotomic bridge first?

Stop after this bounded audit. Do not modify FLT3/FLT5 proof endpoints, do not claim general FLT, and do not enter the later real-cubic / degree-six FUSION machinery.