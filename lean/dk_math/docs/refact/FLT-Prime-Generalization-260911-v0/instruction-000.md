# instruction-000 — FLT7 prime-generalization Lean probe

Branch: `refact/FLT-Prime-Generalization-260911-v0`

Read first:

- `lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/inventory-000.md`
- `lean/dk_math/DkMath/Lib/Cosmic/GTailBoundary.lean`
- `lean/dk_math/DkMath/Lib/Cosmic/GTailCongruence.lean`
- `lean/dk_math/DkMath/Lib/Cosmic/GTailPadic.lean`
- `lean/dk_math/DkMath/Lib/NumberTheory/PadicValNat.lean`
- `lean/dk_math/DkMath/FLT/Seven/CounterexampleRouting.lean`
- `lean/dk_math/DkMath/FLT/Seven/PrimitiveCyclotomicDepth.lean`
- `lean/dk_math/DkMath/FLT/Seven/SevenAdicPowerSplit.lean`

## Goal

Determine, by Lean compilation rather than informal analogy, how much of the front half of the current FLT7 ramified routing is actually a generic prime-exponent GTail theorem.

Do not modify the FLT7 proof tower in this instruction.  Work in a focused test/probe module first.

Create:

```text
lean/dk_math/DkMathTest/FLT/Prime/GeneralizationProbe.lean
lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/report-000.md
```

No `sorry`. No new `axiom`. Do not weaken statements merely to make them compile without recording the reason.

## Probe A — exact r=1 boundary gcd

Prove a theorem of the form

```lean
theorem gcd_GN_prime_eq_gcd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u) :
    Nat.gcd g (DkMath.CosmicFormula.GTail p 1 g u) = Nat.gcd g p := by
  ...
```

Use `DkMath.CosmicFormula.gcd_GTail_eq_gcd_choose`; do not expand `GTail` manually.

Then prove two corollaries:

```text
¬ p ∣ g  -> gcd g (GTail p 1 g u) = 1
p ∣ g    -> gcd g (GTail p 1 g u) = p
```

Record whether primality is actually needed for the first theorem itself, or only for the two branch corollaries.

Expected classification: `CORE-ALREADY` / `PGEN-GREEN`.

## Probe B — prime divisibility address

Attempt the stronger theorem corresponding to current
`seven_dvd_GN_seven_sub_iff`:

```lean
theorem prime_dvd_GN_iff_dvd_gap
    {p g u : ℕ} (hp : Nat.Prime p) :
    p ∣ DkMath.CosmicFormula.GTail p 1 g u ↔ p ∣ g := by
  ...
```

Important: do **not** add `Nat.Coprime g u` unless Lean/math genuinely requires it.
The existing exponent-seven theorem has no coprimality hypothesis.

For the `p ∣ g -> p ∣ GTail ...` direction, reuse existing congruence/boundary infrastructure where practical.

For the reverse direction, inspect the prime Pascal row.  Modulo `p`, all intermediate binomial coefficients vanish and the terminal `g^(p-1)` coefficient remains.  Formalize this with existing Mathlib / GTail lemmas if possible rather than hard-coded expansion.

Check the statement at `p = 2`; the divisibility equivalence is expected to remain valid even though the exact valuation-one theorem below fails there.

If this proof requires a missing reusable prime-row lemma, do not bury it in the test namespace.  Record the minimal missing theorem in `report-000.md` as `PGEN-MISSING-CORE`, with a proposed production location under `DkMath.Lib.Cosmic`.

## Probe C — strengthen the prime-row mod-p² GN convenience theorem

The generic theorem

```lean
GTail_modEq_head_mod_sq_of_prime_dvd_x
```

requires `1 ≤ r` and `r + 1 < p`.
For `r = 1`, this is `2 < p`.

The current convenience theorem

```lean
GN_modEq_head_mod_sq_of_prime_dvd_x
```

instead assumes `5 ≤ p`.

In the probe, establish the sharpened statement without changing production code yet:

```lean
theorem GN_modEq_head_mod_sq_of_odd_prime_dvd_x_probe
    {p : ℕ} (g u : ℕ)
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpg : p ∣ g) :
    DkMath.CosmicFormula.GTail p 1 g u ≡
      p * u ^ (p - 1) [MOD p ^ 2] := by
  ...
```

Derive it directly from the general `GTail_modEq_head_mod_sq_of_prime_dvd_x` with `r = 1`.

If this compiles, mark the existing `5 ≤ p` convenience API as unnecessarily strong and propose a later core cleanup.

## Probe D — exact odd-prime residual valuation

Prove the central candidate:

```lean
theorem padicValNat_GN_prime_eq_one_of_dvd_gap
    {p g u : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    padicValNat p (DkMath.CosmicFormula.GTail p 1 g u) = 1 := by
  ...
```

Preferred proof architecture:

1. use Probe A to obtain `p ∣ GTail p 1 g u`;
2. use primitive coprimality to obtain `¬ p ∣ u`;
3. use Probe C to show `p^2 ∤ GTail p 1 g u`;
4. convert `p ∣ ...` and `¬ p^2 ∣ ...` into the exact valuation `1` using `DkMath.Lib.NumberTheory.PadicValNat`.

Do not use the FLT7 `TraceOneInt (-2)` axis machinery for this proof.  The point is to determine whether the exact-one statement belongs entirely to the generic GTail/valuation layer.

Also add a checked boundary witness showing that the analogous on-channel exact-one statement cannot include `p = 2`.  A suitable arithmetic witness is

```text
GTail 2 1 2 1 = 4
padicValNat 2 4 = 2.
```

Use a checkable Lean example if convenient; otherwise report the evaluated equality together with the reason it blocks the theorem.

## Probe E — generic power-factor split

Generalize the current `seventh_power_factor_split` without reference to FLT7:

```lean
theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d) := by
  ...
```

Use Mathlib's `exists_eq_pow_of_mul_eq_pow` as the current seven proof does.
Record the minimal assumptions Lean actually requires on `d`.

This theorem is not specifically prime-exponent mathematics; if successful it should be marked as a generic reusable factor-splitting lemma rather than an FLT theorem.

## Probe F — generic valuation conservation for p-th-power products

Generalize current `padicValNat_carrier_shape_of_mul_eq_seventh`:

```lean
theorem padicValNat_carrier_shape_of_mul_eq_prime
    {p carrier residual distinguished : ℕ}
    (hp : Nat.Prime p)
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ p)
    (hrVal : padicValNat p residual = 1) :
    ∃ m : ℕ,
      padicValNat p carrier = (p - 1) + p * m := by
  ...
```

Follow the valuation-conservation proof shape of the seven theorem but replace hard-coded arithmetic by prime facts such as `hp.one_lt`.

Do not assume `3 ≤ p` here unless needed.  This algebraic theorem may be valid for `p = 2`; distinguish it from Probe D's odd-prime boundary.

If Lean reveals that the clean natural-number form should instead be written with another equivalent expression, keep both the mathematically natural target and the Lean-convenient intermediate in the report.

## Probe G — divisibility consequence

From Probe F, prove the generic consequence

```text
p^(p-1) ∣ carrier
```

under the same hypotheses.

Use `padicValNat_le_iff_dvd` rather than reconstructing divisibility by hand.

This is the direct general analogue of the current FLT7 conclusion `7^6 ∣ gap`.

## Builds

At minimum run focused builds equivalent to:

```bash
lake build DkMathTest.FLT.Prime.GeneralizationProbe
lake build DkMath.FLT.Seven
```

If production files are unchanged, the second build is a regression check only.

Also run `#print axioms` or the repository's normal axiom-check method for the new main probe theorems.  Report any axioms beyond the ordinary Lean/Mathlib kernel-level ones already accepted by this project.

## Report format

`report-000.md` must contain, for each Probe A–G:

- exact theorem statement that compiled;
- `PGEN-GREEN`, `PGEN-MISSING-CORE`, `PGEN-BOUNDARY`, or `PGEN-FALSE`;
- minimal assumptions found by Lean;
- whether it already follows from `DkMath.Lib.*` or needs a new reusable core theorem;
- relationship to the corresponding FLT7 theorem;
- focused build result and axiom check.

End with a concise decision on whether it is justified to proceed to phase 1: a generic `PrimeAdicPowerSplit` packet with expected normal form

```text
carrier = p^(p-1) * a^p
residual = p * b^p
distinguished = p * a * b.
```

Do not implement that packet in instruction-000.  Its construction depends on the exact results and minimal assumptions found here.
