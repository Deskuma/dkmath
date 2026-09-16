# Codex Instruction — GNPC-008 Arbitrary-Depth Unique Lift / Finite q-Adic Branch

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-007 implementation commit:

```text
0a5c57d713b4cc36b0011becdfa662843dc984f5
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-006.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-007.md
lean/dk_math/DkMath/NumberTheory/GNThreePrimeArithmetic.lean
lean/dk_math/DkMath/NumberTheory/GNThreeHenselLift.lean
```

---

# 0. Purpose

GNPC-007 proved the first simple-root lift for the degree-three GN shell

$$
F_x(u):=GN_3(u,x)=u^2+3ux+3x^2.
$$

For a primitive non-ramified root modulo a prime `q`, it established a unique
next digit `t : Fin q` such that

$$
q^2\mid F_x(u+qt).
$$

The exact mechanism is elementary:

$$
F_x(u+m)=F_x(u)+m(2u+3x)+m^2.
$$

GNPC-008 must generalize this from the first step `q -> q^2` to an arbitrary
finite depth

$$
q^k\to q^{k+1},\qquad k\ge1.
$$

The central result should say:

```text
q^k | GN 3 u x
q ∤ (2*u + 3*x)
k >= 1
      ↓
there exists a unique t : Fin q
      ↓
q^(k+1) | GN 3 (u + q^k*t) x
```

This checkpoint must remain finite and elementary.  Do not construct an
infinite p-adic limit, completion-valued root, or FLT endpoint here.

The interpretation target is that every simple cubic root has a unique
base-`q` continuation at every finite depth for which a representative is
already known.

---

# 1. Mathematical kernel

For every `k,t`, specialize the existing exact shift identity with

```text
m = q^k * t.
```

The required exact identity is

$$
F_x(u+q^kt)
=
F_x(u)+q^kt(2u+3x)+q^{2k}t^2.
$$

If `q^k | F_x(u)`, factor out `q^k`:

$$
F_x(u+q^kt)
=
q^k\left(
\frac{F_x(u)}{q^k}
+t(2u+3x)
+q^kt^2
\right).
$$

For `k >= 1`, the final term `q^k t^2` is divisible by `q`.  Therefore

$$
q^{k+1}\mid F_x(u+q^kt)
\iff
q\mid
\frac{F_x(u)}{q^k}+t(2u+3x).
$$

This is the arbitrary-depth analogue of the private GNPC-007 linearized
criterion.

The unique digit is therefore again

$$
t\equiv
-\frac{F_x(u)}{q^k}(2u+3x)^{-1}
\pmod q.
$$

The derivative remains unchanged modulo `q` along every positive-depth shift:

$$
F_x'(u+q^kt)=F_x'(u)+2q^kt
\equiv F_x'(u)\pmod q.
$$

---

# 2. Mandatory reconnaissance

Before implementation:

1. Search the repository and Mathlib for exact lemmas needed to normalize
   `q^(k+1)` against `q^k * q`, cancel a positive factor from divisibility, and
   prove `q | q^k` under `1 <= k`.

2. Reuse GNPC-007 declarations where possible:

```lean
GN_three_add_boundary_shift
GN_three_add_prime_mul_digit
prime_not_dvd_cubic_boundary_derivative_add_prime_mul
```

Do not duplicate the `q -> q^2` theorem body if the arbitrary-depth theorem can
specialize back to it cleanly.

3. Inspect past FLT-local Hensel material only for theorem/API reconnaissance.
Do not import FLT, Zsigmondy, Kummer, completion, or p-adic application modules
into this NumberTheory owner.

4. Prefer a thin owner:

```text
DkMath/NumberTheory/GNThreeHenselDepth.lean
```

A different owner is acceptable only if repository structure strongly favors
it. Document the choice in `report-008.md`.

---

# 3. Required theorem surface

Exact names may be adjusted slightly after reconnaissance, but preserve the
mathematical layers and record final names/types in the report.

## P0 — arbitrary power-sized shift identity

Preferred theorem:

```lean
theorem GN_three_add_prime_pow_mul_digit
    (q k u x t : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * t) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        q ^ k * t * (2 * u + 3 * x) +
        q ^ (2 * k) * t ^ 2 := by
  ...
```

Reuse `GN_three_add_boundary_shift`; do not re-expand `GN` from `Finset`.

Equivalent exponent normal form such as `(q^k)^2 * t^2` is acceptable if it
makes Lean cleaner, but expose one readable public theorem.

## P1 — arbitrary-depth linearized divisibility criterion

Preferred theorem (public if sufficiently clean; private is acceptable only if
P2/P3 expose all useful consequences):

```lean
theorem pow_succ_dvd_GN_three_add_prime_pow_mul_digit_iff
    {q k u x t : ℕ}
    (hqpos : 0 < q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3 (u + q ^ k * t) x ↔
      q ∣ DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k +
        t * (2 * u + 3 * x) := by
  ...
```

Important proof-engineering point:

- use `Nat.mul_div_cancel' hqkGN` or the exact canonical equivalent;
- rewrite `q^(k+1)` as `q^k * q` in the orientation Mathlib prefers;
- cancel the positive factor `q^k` honestly;
- use `hk` only where needed to show the quadratic remainder contributes a
  multiple of `q` after factoring `q^k`.

Do not smuggle in subtraction or integer division when natural-number exact
division already suffices.

## P2 — generic unique next digit from simple-root data

This is the main GNPC-008 theorem.  Make it more reusable than the application
wrapper by taking derivative nondivisibility directly.

Preferred theorem:

```lean
theorem existsUnique_GN_three_powLift_digit
    {q k u x : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q ^ k * (t : ℕ)) x := by
  ...
```

Solve the same one-variable linear congruence in `ZMod q` as GNPC-007.  Reuse
or factor the duplicated `ZMod` logic if a small local helper makes the code
clearer; avoid premature abstraction into a generic Hensel library.

## P3 — primitive non-ramified application wrapper

Provide the theorem that directly continues the GNPC-006/007 arithmetic route.

Preferred shape:

```lean
theorem existsUnique_GN_three_powLift_digit_of_primitive_nonramified
    {q k u x : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hcop : Nat.Coprime u x)
    (hq3 : q ≠ 3)
    (hqkGN : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q ^ k * (t : ℕ)) x := by
  ...
```

Derive `q | GN 3 u x` from `q^k | GN 3 u x` and `1 <= k`, then invoke
`prime_not_dvd_cubic_boundary_derivative` from GNPC-006, and finally P2.

If a thinner route derives derivative nondivisibility from the current lifted
representative using GNPC-007 stability, document it.  Do not add stronger
hypotheses than necessary.

## P4 — derivative stability at arbitrary positive depth

Generalize GNPC-007 P5.

Preferred theorem:

```lean
theorem prime_not_dvd_cubic_boundary_derivative_add_prime_pow_mul
    {q k u x t : ℕ}
    (hk : 1 ≤ k)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q ^ k * t) + 3 * x := by
  ...
```

Mathematically the only point is `q | q^k` for `k >= 1`.

If the existing GNPC-007 theorem can be reused by writing `q^k*t` as
`q*(q^(k-1)*t)`, prefer whichever proof is clearer and less brittle.

## P5 — arbitrary-depth explicit correction digit

Expose the finite-depth Newton/Hensel correction formula in `ZMod q`.

Preferred definition:

```lean
def GNThreeNextPowLiftDigitZMod
    (q k u x : ℕ) [Fact q.Prime] : ZMod q :=
  -((DkMath.CosmicFormulaBinom.GN 3 u x / q ^ k : ℕ) : ZMod q) *
    ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹
```

Add a correctness theorem saying any `t : Fin q` satisfying the
`q^(k+1)`-lift condition equals/casts to this displayed correction under the
P2 hypotheses.

Do not define this as a global total "next digit" semantics without hypotheses;
its algebraic formula is total in `ZMod`, but its Hensel interpretation depends
on simple-root data and exact `q^k` divisibility.

## P6 — specialization back to GNPC-007

Add a thin regression theorem or example showing that `k = 1` recovers the
GNPC-007 result.  It need not replace the existing theorem yet.

For example:

```lean
example
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ∃! t : Fin q,
      q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3
        (u + q * (t : ℕ)) x := by
  ...
```

The proof should be a specialization of the arbitrary-depth theorem, not a copy
of GNPC-007's original proof.

---

# 4. Mandatory depth-3 regressions for q = 7, x = 1

GNPC-007 fixed the mod-49 branches

```text
1 mod 7  -> 29 mod 49
3 mod 7  -> 17 mod 49
```

GNPC-008 must extend these by one more digit and verify uniqueness using the
generic theorem.

The expected depth-3 continuations are:

```text
29 + 49*6 = 323
17 + 49*0 = 17
```

Thus verify at least:

```lean
example : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 323 1 := by
  ...

example : 7 ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  ...
```

and uniqueness of the next digits:

```text
from u = 29 at k = 2, only t = 6 works;
from u = 17 at k = 2, only t = 0 works.
```

The second case is particularly useful conceptually: `GN 3 17 1 = 7^3`, so
its mod-49 representative already lies on the mod-343 branch and therefore its
next digit is zero.

Do not infer from these examples that the next digit remains zero at deeper
levels.

---

# 5. Strongly preferred optional finite-branch layer

Only after P0-P6 are complete and clean, consider exposing a finite branch
constructor.  Keep this bounded and elementary.

One acceptable direction is a recursive state carrying a representative
`u_k` and proof

```text
q^k | GN 3 u_k x
```

with transition

```text
u_(k+1) = u_k + q^k * digit_k.
```

A possible theorem-level API is sufficient; a large structure is not required.
For example, prove by induction that from a primitive non-ramified root modulo
`q` and any target depth `n >= 1`, there exists a representative `v` with

```text
v ≡ u [MOD q]
q^n | GN 3 v x.
```

Uniqueness should only be claimed modulo `q^n` if it is actually proved.

Do not construct an infinite sequence or invoke completeness in GNPC-008.

---

# 6. Interpretation boundary

The report must distinguish carefully:

1. GNPC-006: non-ramified primitive cubic roots are simple.
2. GNPC-007: every such root has one unique lift digit from `q` to `q^2`.
3. GNPC-008: the same local mechanism works at every finite positive depth.
4. Therefore prime-power divisibility corresponds to following a unique finite
   base-`q` branch, not to an exceptional failure of squarefreeness.
5. This still does **not** classify the valuation of a fixed arbitrary integer
   coordinate without comparing that coordinate to the canonical branch.
6. This still does **not** prove FLT3 or replace `hS0_not_sq` by itself.

The future FLT3 question becomes:

```text
Given the actual Fermat-derived gap coordinate,
for how many q-adic digits does it agree with the unique cubic GN branch?
```

That is a branch-address / valuation-depth question.

---

# 7. Non-goals

Do not include in GNPC-008:

- p-adic completions or `ℚ_[q]` / `ℤ_[q]` roots;
- infinite Hensel sequences;
- a full valuation equality theorem for arbitrary coordinates;
- Eisenstein UFD descent;
- FLT3 endpoint changes;
- removal/replacement of `hS0_not_sq`;
- FLT5/FLT7 refactors;
- generic-degree Hensel theory;
- a general polynomial Hensel library unless absolutely required by a reused
  Mathlib theorem.

---

# 8. Validation

At minimum run:

```bash
lake build DkMath.NumberTheory.GNThreeHenselDepth
```

If the final owner name differs, build that module explicitly.

Also confirm:

- no new `sorry`;
- no new `axiom`;
- no Lean warnings in the new module;
- no heavy FLT/Zsigmondy import was introduced.

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-008.md
```

The report must contain:

- outcome A/B/C;
- final theorem surface and exact types;
- exact Mathlib divisibility/power lemmas reused;
- whether P1 was public or private and why;
- q=7 depth-3 regression results;
- whether the optional finite-branch layer was attempted;
- explicit statement that infinite p-adic completion and FLT3 remain deferred.

---

# 9. Definition of Done

GNPC-008 is complete when Lean proves, without new `sorry`/`axiom`, the finite
arbitrary-depth local statement:

$$
\boxed{
q^k\mid GN_3(u,x),\quad
q\nmid(2u+3x),\quad
k\ge1
\Longrightarrow
\exists!\,t\in\{0,\ldots,q-1\}:\
q^{k+1}\mid GN_3(u+q^kt,x)
}
$$

and the primitive non-ramified GN wrapper derives the derivative hypothesis
from the established GNPC-006 arithmetic.

This theorem is the finite-depth branch engine needed before translating FLT3
square-lift assumptions into exact branch-address / valuation-depth language.
