# Codex Instruction — GNPC-007 Degree-3 Simple-Root Hensel Lift / Unique Prime-Power Branch

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-006 implementation commit:

```text
e792091471b7a15f33aafb604dbde829aa354c2c
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-005.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-006.md
lean/dk_math/DkMath/NumberTheory/GNThreeQuadratic.lean
lean/dk_math/DkMath/NumberTheory/GNThreePrimeArithmetic.lean
```

---

# 0. Purpose

GNPC-006 established the arithmetic split of the primitive cubic GN shell

$$
F_x(u):=GN_3(u,x)=u^2+3ux+3x^2.
$$

For a prime divisor `q != 3` on coprime coordinates, it proved

```text
q | F_x(u)
q ∤ 2*u + 3*x
3 | q - 1
```

where

$$
F_x'(u)=2u+3x.
$$

It also proved that square lifts really occur, for example

$$
GN_3(17,1)=343=7^3.
$$

Therefore the correct next step is not a no-lift theorem.  GNPC-007 must show that every non-ramified primitive cubic root is a **simple modular root**, and that its residue class has a **unique next base-`q` digit** lifting it from modulus `q` to modulus `q^2`.

The preferred implementation is elementary and integral.  Do not jump directly to abstract `ℚ_[q]`, completions, or a large Hensel framework unless repository reconnaissance proves that Mathlib already provides a very thin theorem matching this exact use case.

The main conceptual target is:

```text
q | GN 3 u x
q prime, q != 3, Coprime u x
        ↓
q ∤ (2*u + 3*x)
        ↓
there exists a unique digit t in {0,...,q-1}
        ↓
q^2 | GN 3 (u + q*t) x
```

This is the first exact prime-power branch theorem for GN Prime Closure.

---

# 1. Mandatory reconnaissance

Before writing the new owner:

1. Search DkMath for existing lemmas equivalent to:
   - the exact shift/Taylor identity for `GN 3`;
   - a modular simple-root lift from `q` to `q^2`;
   - a `Fin q` unique digit representation of a residue modulo `q`;
   - any existing Hensel helper specialized to `Nat`, `Int`, `ZMod`, or quadratic polynomials.

2. Search Mathlib locally for the exact available Hensel APIs, especially around:
   - `Polynomial` Hensel lemmas;
   - roots modulo prime powers;
   - `ZMod` inverses for prime modulus;
   - existence/uniqueness of a residue representative in `Fin q` / `ZMod q`;
   - cancellation of a nonzero coefficient in `ZMod q`.

3. Do not force a heavy abstract Hensel import if the elementary quadratic proof is much smaller.  Record the exact Mathlib route chosen in `report-007.md`.

4. Prefer a thin new owner:

```text
DkMath/NumberTheory/GNThreeHenselLift.lean
```

A different owner is acceptable only if reconnaissance finds a clearly better existing NumberTheory location.

---

# 2. Core exact shift identity

The mathematical engine is the exact quadratic Taylor identity

$$
F_x(u+m)=F_x(u)+m(2u+3x)+m^2.
$$

For the GN kernel:

$$
GN_3(u+m,x)
=
GN_3(u,x)+m(2u+3x)+m^2.
$$

This must be proved once from `GN_three_dual_explicit`; do not expand `GN` through `Finset` again.

## P0 — generic cubic shift identity

Preferred theorem:

```lean
theorem GN_three_add_boundary_shift
    (u x m : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + m) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        m * (2 * u + 3 * x) + m ^ 2 := by
  ...
```

Equivalent multiplication association/order is acceptable if it is more stable for later divisibility proofs.

## P1 — prime-step specialization

Expose the exact `m = q*t` form:

```lean
theorem GN_three_add_prime_mul_digit
    (q u x t : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 (u + q * t) x =
      DkMath.CosmicFormulaBinom.GN 3 u x +
        q * t * (2 * u + 3 * x) + q ^ 2 * t ^ 2 := by
  ...
```

This should be a thin corollary of P0 plus `ring`/normalization.

---

# 3. One-digit lifting equation

Assume

```text
q | F_x(u).
```

Write

$$
F_x(u)=qC.
$$

Then P1 gives

$$
F_x(u+qt)=q\left(C+t(2u+3x)+qt^2\right).
$$

Hence

$$
q^2\mid F_x(u+qt)
$$

is equivalent to the linear congruence

$$
C+t(2u+3x)\equiv0\pmod q.
$$

The `q t^2` term vanishes modulo `q`.

GNPC-006 already proves that for a non-ramified primitive root

$$
q\nmid2u+3x,
$$

so this linear congruence has exactly one solution modulo `q`.

Implementation note: it is acceptable to use `C = F_x(u) / q` after proving the exact multiplication identity from `q | F_x(u)`.  It is also acceptable to destruct the divisibility witness `F_x(u) = q*C` internally and avoid exposing a quotient-heavy API.  Prefer whichever route gives the smallest stable public theorem surface.

## P2 — linear lift criterion

Strongly preferred public theorem, if the quotient/cast statement stays clean:

```lean
theorem sq_dvd_GN_three_add_prime_mul_digit_iff
    {q u x t : ℕ}
    (hq : Nat.Prime q)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (u + q * t) x ↔
      q ∣ DkMath.CosmicFormulaBinom.GN 3 u x / q +
        t * (2 * u + 3 * x) := by
  ...
```

Adjust parentheses and the exact quotient expression as needed.

If this public quotient theorem becomes brittle, keep the equivalent statement private and proceed directly to P3.  Do not spend the checkpoint on cosmetic quotient normalization.

---

# 4. Main theorem — unique lift digit from `q` to `q^2`

This is the required endpoint.

Use `Fin q` if practical.  It gives the canonical digit range automatically and turns uniqueness modulo `q` into literal uniqueness.

## P3 — unique next digit

Preferred theorem:

```lean
theorem existsUnique_GN_three_sqLift_digit
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ∃! t : Fin q,
      q ^ 2 ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q * (t : ℕ)) x := by
  ...
```

Required dependency direction:

```text
GNPC-006 prime_not_dvd_cubic_boundary_derivative
        ↓
coefficient (2*u+3*x) is a unit in ZMod q
        ↓
unique linear digit t mod q
        ↓
P0/P1 exact shift identity
        ↓
q^2 | GN 3 (u + q*t) x
```

Do not reprove the derivative exclusion inside this theorem.

If `Fin q` causes disproportionate coercion overhead, an acceptable alternative is

```lean
∃! t : ℕ,
  t < q ∧
  q ^ 2 ∣ GN 3 (u + q * t) x
```

but prefer `Fin q` if the proof remains clean.

---

# 5. Explicit lift-digit formula

If it remains thin, expose the actual modular Newton/Hensel digit.

For

$$
C=F_x(u)/q,
\qquad
D=2u+3x,
$$

the unique digit satisfies

$$
t\equiv-C D^{-1}\pmod q.
$$

## P4 — optional-but-preferred formula API

Possible definition under prime modulus:

```lean
def GNThreeNextLiftDigitZMod
    (q u x : ℕ) [Fact q.Prime] : ZMod q :=
  -((DkMath.CosmicFormulaBinom.GN 3 u x / q : ℕ) : ZMod q) *
    ((2 * u + 3 * x : ℕ) : ZMod q)⁻¹
```

Then prove, under the P3 hypotheses, that the unique `Fin q` digit maps to this `ZMod q` value.

Do not make P3 depend on this definition if doing so complicates the proof unnecessarily.  The existence/uniqueness theorem is more important than the exposed closed formula.

---

# 6. Lift preserves the same simple-root branch modulo `q`

A lifted coordinate

$$
u'=u+qt
$$

satisfies

$$
u'\equiv u\pmod q.
$$

Therefore its derivative is congruent to the original derivative:

$$
2u'+3x\equiv2u+3x\pmod q.
$$

This is what permits iteration to higher powers without re-running the global primitive-coordinate argument at each step.

## P5 — derivative nondegeneracy is stable under one lift

Preferred theorem:

```lean
theorem prime_not_dvd_cubic_boundary_derivative_add_prime_mul
    {q u x t : ℕ}
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ¬ q ∣ 2 * (u + q * t) + 3 * x := by
  ...
```

This theorem is elementary and should not require primality.

A `Nat.ModEq` formulation is equally acceptable if cleaner.

---

# 7. Mandatory regressions — the two roots above `q = 7`

For `x = 1`,

$$
F(u)=u^2+3u+3.
$$

Modulo `7`, the two roots are represented by `u = 1` and `u = 3`.

Their unique lifts modulo `49` are:

```text
u = 1  -> digit t = 4 -> 1 + 7*4 = 29
u = 3  -> digit t = 2 -> 3 + 7*2 = 17
```

Required lightweight regressions:

```lean
example : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 1 1 := by
  ...

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 29 1 := by
  ...

example : 7 ∣ DkMath.CosmicFormulaBinom.GN 3 3 1 := by
  ...

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  ...
```

Also record the exact unique digits through P3 if this can be done without large proof noise.  At minimum the report must state that the generic unique-lift theorem specializes to the digits `4` and `2` respectively.

Retain the GNPC-006 fact

$$
GN_3(17,1)=7^3
$$

as interpretation: the `u = 3 mod 7` branch lifts to `u = 17 mod 49`, and this representative happens to have valuation at least three.

Do **not** infer from this single representative that every mod-`49` root automatically has valuation exactly three.

---

# 8. Strongly preferred optional extension — one step at arbitrary depth

Only after P0–P5 and the regressions are clean, attempt the general one-step theorem.

For `k >= 1`, assume

$$
q^k\mid F_x(u)
$$

and

$$
q\nmid F_x'(u).
$$

Then there should be a unique digit `t mod q` such that

$$
q^{k+1}\mid F_x(u+q^k t).
$$

The same exact identity gives

$$
F_x(u+q^k t)
=
F_x(u)+q^k tF_x'(u)+q^{2k}t^2,
$$

and `k >= 1` guarantees

$$
q^{k+1}\mid q^{2k}t^2.
$$

Suggested theorem:

```lean
theorem existsUnique_GN_three_nextPrimePowerLift_digit
    {q k u x : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqk : q ^ k ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hqder : ¬ q ∣ 2 * u + 3 * x) :
    ∃! t : Fin q,
      q ^ (k + 1) ∣
        DkMath.CosmicFormulaBinom.GN 3
          (u + q ^ k * (t : ℕ)) x := by
  ...
```

This theorem is optional for GNPC-007.  If it requires a disproportionately large divisibility-normalization layer, stop after the validated `q -> q^2` theorem and describe the exact blocker in the report.

Do not construct an infinite `q`-adic sequence in this checkpoint.

---

# 9. Interpretation boundary

The module/report must state clearly:

1. GNPC-006 showed that non-ramified primitive cubic roots are simple modulo `q`.
2. GNPC-007 shows that each such root determines one unique next digit modulo `q^2`.
3. Therefore square lift is not an exceptional pathology; it is the expected unique continuation of a simple split-sector root.
4. A statement `q^2 ∤ GN3` cannot be the generic arithmetic kernel for FLT3.
5. The future FLT3 question is instead whether a Fermat-derived packet can occupy a lift branch of depth at least two, and what Eisenstein/unit/descent structure that occupancy forces.

Do not claim that GNPC-007 proves FLT3, removes `hS0_not_sq`, or classifies all prime-power valuations.

---

# 10. Forbidden scope expansion

Do not implement in GNPC-007:

- changes to `DkMath.FLT` or the FLT3 endpoint;
- a global replacement for `hS0_not_sq`;
- p-adic completions / `ℚ_[q]` / `ℤ_[q]` unless absolutely required by a very thin existing Mathlib theorem;
- an infinite Hensel sequence or inverse limit;
- full valuation classification `v_q(GN3)`;
- Eisenstein UFD factorization or unit descent;
- cyclotomic/Zsigmondy refactors;
- general degree `d` Hensel theory;
- FLT5/FLT7 modifications;
- ABC / Legendre / RH applications.

Keep this checkpoint focused on the one-step simple-root lift mechanism.

---

# 11. Validation

Expected build target:

```text
lake build DkMath.NumberTheory.GNThreeHenselLift
```

Requirements:

- no new `sorry`;
- no new `axiom`;
- no warning-producing unused arguments;
- thin imports;
- reuse GNPC-006 derivative theorem rather than duplicating it;
- no changes to existing FLT application behavior.

---

# 12. Required report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-007.md
```

Include:

1. Outcome A / B / C.
2. Exact DkMath/Mathlib Hensel or modular APIs found during reconnaissance.
3. Final owner module and imports.
4. Final theorem types P0–P5.
5. Whether P2 quotient criterion was public or kept private.
6. Whether the explicit modular digit formula P4 was added.
7. `q = 7`, `x = 1` regression results, including the two lifts `1 -> 29` and `3 -> 17` and digits `4`, `2` when verified.
8. Whether the arbitrary-depth optional theorem was completed.
9. Build result.
10. Deferred FLT3 / valuation / p-adic work.

---

# 13. Stop condition

STOP when the following is formally available and validated:

```text
q prime, q != 3
Coprime u x
q | GN 3 u x
        ↓
q ∤ (2*u + 3*x)                  [GNPC-006]
        ↓
∃! digit t mod q
        ↓
q^2 | GN 3 (u + q*t) x           [GNPC-007]
```

and the `q = 7`, `x = 1` branches visibly reproduce

```text
1 mod 7 -> 29 mod 49
3 mod 7 -> 17 mod 49.
```

Do not continue automatically into FLT3 or infinite prime-power lifting.