# PRIM-L038 — Möbius Exact Reduced-Residue Wave Occupancy / Divisor-Floor Ledger Lean Judgment

Date: 2026-08-26
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

## 0. Purpose

PRIM-L037 normalized every parity-safe active prime wave into the finite set

```text
Ioc ((n^2)/q) ((n^2+2*n)/q)
  filtered by Nat.Coprime (2*n)
```

and proved an exact cardinality bijection with `paritySafeActiveWaveOffsets n q`.

Do not add another coordinate-only wrapper and do not return to the L036 silent/uncovered ledger.  The next task is to open the reduced-residue count itself by finite Möbius inclusion-exclusion.

The intended new information is an exact signed divisor-floor formula.  This is still finite arithmetic: no PNT, asymptotic density, analytic sieve, Jacobsthal bound, RH/CFBRC, or Legendre theorem.

## 1. New module

Create:

```text
DkMath/NumberTheory/Legendre/ParitySafeMobiusWave.lean
```

Suggested imports:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
```

Add it to `DkMath/NumberTheory/Legendre.lean`.

Keep generic helper lemmas local/private when they are only scaffolding.  Public declarations should describe the finite counting result or its Legendre specialization.

## 2. Generic finite coprime-Ioc Möbius formula

For positive modulus `M`, prove an exact integer-valued formula of the following mathematical shape.

For `A ≤ B`,

```text
#{ k : A < k ≤ B, gcd(M,k)=1 }
  = Σ_{d|M} μ(d) * ( floor(B/d) - floor(A/d) ).
```

Because Möbius values are signed, state the equality in `ℤ`, not `ℕ`.

A target shape is conceptually:

```lean
theorem card_filter_coprime_Ioc_eq_sum_moebius_div
    {M A B : ℕ}
    (hM : 0 < M) :
    (((Finset.Ioc A B).filter (fun k => Nat.Coprime M k)).card : ℤ) =
      ∑ d ∈ M.divisors,
        ArithmeticFunction.moebius d *
          (((B / d : ℕ) : ℤ) - ((A / d : ℕ) : ℤ)) := by
  ...
```

Exact theorem spelling may change to fit Mathlib APIs, but preserve this mathematical statement.

Useful proof route:

1. For each `k`, expand the coprime indicator by divisors of `gcd M k`:

   ```text
   1[gcd(M,k)=1] = Σ_{d | gcd(M,k)} μ(d).
   ```

2. Swap the finite sums.
3. For fixed positive divisor `d | M`, count multiples of `d` in `Ioc A B` by

   ```text
   B / d - A / d.
   ```

`Wave.lean` already uses the corresponding exact finite multiple-count mechanism (`Nat.Ioc_filter_dvd_card_eq_div`). Reuse existing arithmetic rather than rebuilding interval counting from scratch.

If Mathlib's Möbius convolution lemmas are easier than proving the indicator identity directly, use them. Do not introduce an axiom or a bespoke Möbius definition.

## 3. Specialize to the parity-safe reduced quotient interval

Using L037, prove an exact formula for each active prime wave.

For

```text
A_q := (n^2) / q
B_q := (n^2 + 2*n) / q
M   := 2*n
```

prove, in `ℤ`, the mathematical identity

```text
(card (paritySafeActiveWaveOffsets n q) : ℤ)
  = Σ_{d | 2*n} μ(d) * (B_q/d - A_q/d).
```

Suggested public theorem name:

```lean
paritySafeActiveWave_card_eq_mobius_divisor_floor_sum
```

Require the existing active-prime membership hypothesis and `0 < n` only when genuinely needed.

The theorem must use the L037 wave/quotient bijection; do not re-prove the wave correspondence.

## 4. Global incidence Möbius rewrite

Rewrite `paritySafeIncidenceCount n` exactly as the sum of the Möbius wave formulas:

```text
Incidence(n)
  = Σ_{q active} Σ_{d | 2*n}
      μ(d) * Δfloor(n,q,d).
```

Then commute the two finite sums and expose the divisor-first form:

```text
Incidence(n)
  = Σ_{d | 2*n} μ(d) *
      Σ_{q active} Δfloor(n,q,d).
```

Use `ℤ` throughout the signed ledger.

A small helper definition for the nonnegative floor difference is acceptable, for example

```lean
def paritySafeQuotientDivisorFloorDelta (n q d : ℕ) : ℕ :=
  ((n^2 + 2*n) / q) / d - ((n^2) / q) / d
```

but avoid creating several redundant aliases.

## 5. Isolate the `d = 1` main term from the signed correction

If cleanly supported by Mathlib's divisor API, split the exact formula into:

```text
Incidence = rawIntervalMass + mobiusCorrection
```

where the `d=1` contribution is the unsigned raw quotient interval length

```text
Σ_{q active} (B_q - A_q)
```

and all divisors `d > 1` remain in a signed Möbius correction.

Possible definitions:

```lean
paritySafeRawQuotientIntervalMass
paritySafeMobiusCorrection
```

The exact equality is the goal; no sign or asymptotic estimate for the correction is required.

Do not force this section if the only way to obtain it is a large brittle rewrite around `Nat.divisors.erase 1`.  In that case report the exact obstruction and keep the divisor-first formula from section 4 as the terminal theorem.

## 6. Concrete Lean sanity witness

Use a small actual wave to confirm that the signed formula records real cancellation rather than merely renaming the count.

Preferred witness:

```text
n = 5
q = 3
```

Here the parity-safe wave has the two candidate seats corresponding to complete points `27` and `33`, and its quotient interval is the reduced-residue interval for modulus `10`.

Prove a small theorem showing at least:

```text
(paritySafeActiveWaveOffsets 5 3).card = 2
```

and, if reasonably short, that the Möbius divisor-floor side also evaluates to `2`.

Do not add a large table or `native_decide`.

## 7. Stronger-beam judgment

The report must answer explicitly:

1. Did the short reduced-residue quotient count become an exact finite Möbius divisor-floor sum?
2. Did the global incidence count transpose to a divisor-first signed sum?
3. Could the `d=1` raw term be separated cleanly from the signed correction?
4. Does the formula expose genuine cancellation on a concrete small wave?
5. Does any theorem actually bound the signed correction strongly enough to imply the L035/L036 frontier universally?

Expected classifications:

```text
Outcome A — EXACT MÖBIUS DIVISOR-FLOOR / CANCELLATION FRONTIER
  Generic finite formula + wave specialization + global divisor-first rewrite succeed.
  Preferably also isolate the d=1 term.

Outcome B — EXACT LOCAL MÖBIUS WAVE FORMULA ONLY
  Local exact formula succeeds, but a clean global transpose or main/correction split does not.

Outcome C — NO MATERIAL MÖBIUS OPENING
  Only existing reduced-residue cardinalities are restated; no signed divisor-floor identity is proved.
```

Outcome A does **not** mean Legendre's conjecture is proved.  Unless a genuinely new universal bound appears, stop after exposing the signed finite cancellation frontier.

## 8. Stop boundary

Do not introduce:

- analytic prime counting or PNT,
- Mertens estimates,
- Jacobsthal bounds,
- generic sieve libraries,
- graph/matching abstractions,
- descent,
- RH/CFBRC dependencies,
- `LegendreConjecture` as a proved theorem.

Do not modify L025--L037 public theorem statements unless a real correctness bug is found.

## 9. Validation

Run:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeMobiusWave
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Audit the new Lean source for trailing whitespace and forbidden placeholders (`sorry`, `admit`, `axiom`, `native_decide`).

Write the judgment report to:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-mobius-wave-divisor-floor-260826.md
```

Stop after the report. Do not commit/push/CI from the implementation agent unless separately instructed.
