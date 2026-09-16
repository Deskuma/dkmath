# Codex Instruction — GNPC-006 Degree-3 Prime Shell Arithmetic / Eisenstein Split & Square-Lift Classification

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-005 implementation commit:

```text
75bbd9bbc6efd4c0dc4863442aa4360893e245ff
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-004.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-005.md
lean/dk_math/DkMath/NumberTheory/GNPrimeTargetResidue.lean
lean/dk_math/DkMath/NumberTheory/GNThreeQuadratic.lean
lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
```

Also inspect, for reconnaissance only, the existing FLT3 / Zsigmondy material that already uses the same cubic kernel. Do not import heavy FLT/Zsigmondy modules into the new NumberTheory owner unless absolutely unavoidable.

---

# 0. Purpose

GNPC-005 established the exact degree-three shell

$$
GN_3(u,x)=u^2+3ux+3x^2
$$

and

$$
4GN_3(u,x)=u^2+3(2x+u)^2.
$$

It also identified `GN 3 u x` with the discriminant `-3` trace-one norm.

GNPC-006 must now study the arithmetic of prime divisors of this shell.

The motivating distinction is important:

- a general statement saying "prime divisors of the cubic shell never square-lift" is false;
- the ramified prime `3` behaves differently from the split prime sector;
- on primitive coordinates, `3` should occur with multiplicity at most one;
- any prime square-lift should therefore lie away from `3`, and the expected non-ramified prime sector is `q ≡ 1 (mod 3)`;
- explicit square-lift examples exist, so the correct theory is classification, not prohibition.

This checkpoint is deliberately pure NumberTheory. Do **not** modify the FLT3 endpoint or try to prove FLT3 here.

---

# 1. Current structural facts to reuse

GNPC-004 gives, for a positive prime-target representation,

```lean
GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime
GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
```

so at degree `3`, a prime target satisfies

```text
3 ∤ u
3 ∣ p - 1.
```

GNPC-005 gives:

```lean
GN_three_dual_explicit
GN_three_eq_discriminant_neg_three_form
GN_three_eq_traceOneNorm_negOne
four_mul_GN_three_eq_centered_square
GN_three_eq_target_iff_centered_square
GNThreeCenteredResidual
GN_three_eq_target_iff_centeredResidual_eq_zero
```

The existing gcd layer already contains, in `DkMath.NumberTheory.Gcd.GN`, the degree-three boundary facts

```lean
gcd_boundary_GN_three_eq_gcd_boundary_three
gcd_boundary_GN_three_dvd_three
coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

under primitive/coprime coordinates. Reuse these where the orientation matches. For the dual-oriented shell, substitute the boundary argument accordingly rather than reproving the same gcd theorem from scratch.

The same gcd owner also contains generic no-square-lift-from-squarefree and valuation bridge utilities. These are supporting APIs only; GNPC-006 must not assume the cubic GN shell is squarefree.

---

# 2. Critical mathematical correction to preserve

The current DkMath-native FLT3 valuation route still has an additional no-square-lift input. That condition is **not** a universal theorem about the cubic GN kernel.

A concrete counterexample is

$$
GN_3(17,1)=17^2+3\cdot17\cdot1+3\cdot1^2=343=7^3.
$$

Therefore

$$
7^2\mid GN_3(17,1).
$$

This checkpoint must explicitly record this example so that future work does not attempt to prove a false global no-square-lift theorem.

The correct target is:

```text
primitive cubic shell
  ├─ ramified q = 3 sector: no square lift
  └─ non-ramified prime sector: q ≡ 1 mod 3
       └─ square lifts may actually occur
```

---

# 3. Mandatory reconnaissance before implementation

Before editing:

1. Search the repository for existing theorems equivalent to:
   - `3 ∣ GN 3 u x ↔ 3 ∣ u`;
   - `Nat.Coprime u x → ¬ 9 ∣ GN 3 u x`;
   - prime divisor `q ≠ 3` of `GN 3 u x` forcing `3 ∣ q - 1`;
   - primitive-prime / multiplicative-order theorems that already imply the previous item;
   - a direct theorem that a prime divisor of the degree-three cyclotomic factor is `1 mod 3` away from the ramified prime.

2. Inspect the exact namespaces/types of the existing degree-three gcd theorems in `DkMath.NumberTheory.Gcd.GN`.

3. Search Mathlib for the weakest canonical route for:
   - a nontrivial cubic root of unity modulo a prime `q`;
   - `orderOf` / finite multiplicative group cardinality;
   - concluding `3 ∣ q - 1` from an element of exact order `3`;
   - prime divisors of cyclotomic polynomials, if there is already a theorem specialized enough to avoid rebuilding the order argument.

Do not guess theorem names in the final code. Record the exact reused Mathlib theorem(s) in the report.

4. Prefer a thin new owner:

```text
DkMath/NumberTheory/GNThreePrimeArithmetic.lean
```

Document a different owner choice if reconnaissance finds a clearly better existing location.

---

# 4. Required theorem surface

Exact names may be adjusted slightly after reconnaissance, but preserve the mathematical layers.

## P0 — the ramified prime criterion

Prove the exact degree-three mod-3 criterion.

Preferred theorem:

```lean
theorem three_dvd_GN_three_iff_dvd_boundary
    {u x : ℕ} :
    3 ∣ DkMath.CosmicFormulaBinom.GN 3 u x ↔ 3 ∣ u := by
  ...
```

Reason: from

$$
GN_3(u,x)=u^2+3ux+3x^2
$$

we have

$$
GN_3(u,x)\equiv u^2\pmod3.
$$

Use the existing cubic explicit theorem; do not expand `GN` through `Finset` again.

## P1 — the ramified prime does not square-lift on primitive coordinates

Preferred theorem:

```lean
theorem not_nine_dvd_GN_three_of_coprime
    {u x : ℕ}
    (hcop : Nat.Coprime u x) :
    ¬ 9 ∣ DkMath.CosmicFormulaBinom.GN 3 u x := by
  ...
```

Equivalent exact valuation form at `3` is acceptable if existing APIs make it cleaner, but keep a divisibility wrapper with the above meaning.

Suggested proof split:

- if `3 ∤ u`, P0 already gives `3 ∤ GN`, hence no `9`;
- if `3 ∣ u`, write `u = 3k`;
- then

$$
GN_3(3k,x)=3(3k^2+3kx+x^2);
$$

- coprimality gives `3 ∤ x`, hence the parenthesized factor is nonzero modulo `3`;
- therefore exactly one factor of `3` occurs.

Do not introduce FLT-specific `S0` vocabulary here.

## P2 — common boundary divisors away from `3` are impossible

Expose a thin prime-divisor helper if useful.

Suggested shape:

```lean
theorem prime_not_dvd_boundary_of_dvd_GN_three_of_coprime_of_ne_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ¬ q ∣ u := by
  ...
```

Prefer reusing `gcd_boundary_GN_three_dvd_three` with the dual orientation.

If a similarly useful `¬ q ∣ x` theorem remains thin, add it as well. It is useful for the multiplicative-order proof because `x` must be invertible modulo `q`.

## P3 — non-ramified prime divisors lie in the `1 mod 3` sector

This is the main arithmetic theorem of GNPC-006.

Preferred theorem:

```lean
theorem three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    3 ∣ q - 1 := by
  ...
```

Equivalent `Nat.ModEq 3 q 1` output is acceptable, but provide a thin divisibility wrapper if practical.

Recommended mathematical route if no direct cyclotomic theorem is available:

Let

```text
a = x + u
b = x.
```

From `q ∣ GN 3 u x`,

$$
q\mid a^3-b^3.
$$

From P2 / coprimality, `q ∤ u`, so `a` and `b` are distinct modulo `q`; also establish `q ∤ b`.

In `ZMod q`, the ratio

$$
r=a/b
$$

then satisfies

$$
r^3=1,
$$

but

$$
r\ne1.
$$

Since `3` is prime, the multiplicative order of `r` is exactly `3`. The order divides the cardinality `q - 1` of the unit group, hence

$$
3\mid q-1.
$$

Do not build a large custom group theory layer. Search Mathlib first.

If a direct Mathlib cyclotomic-prime-divisor theorem gives this with much less proof engineering, prefer it and document the exact route.

## P4 — square-lift primes are necessarily non-ramified split-sector primes

Preferred theorem:

```lean
theorem three_dvd_prime_sub_one_of_square_lift_GN_three
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hq2 : q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 u x) :
    3 ∣ q - 1 := by
  ...
```

Dependency:

```text
q^2 ∣ GN3
  ↓
q ∣ GN3
  ↓
q ≠ 3              by P1
  ↓
3 ∣ q - 1          by P3
```

This theorem is the primary square-lift classification endpoint for GNPC-006.

Do **not** claim the converse. `q ≡ 1 mod 3` does not by itself force a given coordinate pair `(u,x)` to square-lift.

## P5 — prime-target coordinates are primitive

For a prime target represented at degree `3`, prove that the two positive GN coordinates are coprime.

Preferred theorem:

```lean
theorem GNPositiveRepresentation.coprime_coordinates_of_degree_three_target_prime
    {p u x : ℕ}
    (hrep : GNPositiveRepresentation p 3 u x)
    (hp : Nat.Prime p) :
    Nat.Coprime u x := by
  ...
```

Use the already-proved finite bounds and target equality where useful. Avoid importing Eisenstein UFD machinery just to prove a simple primitive-coordinate fact.

One practical route:

- let `g = gcd u x`;
- show `g ∣ GN 3 u x = p` from the explicit quadratic form;
- `g ≤ u < p` from the representation bounds;
- primality of `p` excludes a divisor strictly between `1` and `p`;
- conclude `g = 1`.

Adjust the proof if Mathlib has a cleaner coprime criterion.

## P6 — package the degree-three prime shell

Add one theorem assembling the already-proved constraints.

Preferred shape:

```lean
theorem GNPositiveRepresentation.degree_three_prime_shell_constraints
    {p u x : ℕ}
    (hrep : GNPositiveRepresentation p 3 u x)
    (hp : Nat.Prime p) :
    Nat.Coprime u x ∧
      ¬ 3 ∣ u ∧
      3 ∣ p - 1 ∧
      4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  ...
```

All parts except coordinate coprimality should be thin compositions of GNPC-004 and GNPC-005. Do not reprove the residue or centered-square theory.

Conjunction ordering may be adjusted for Lean ergonomics; document the exact final type.

---

# 5. Mandatory square-lift regression

Record the explicit non-ramified lift:

```lean
example : DkMath.CosmicFormulaBinom.GN 3 17 1 = 343 := by
  ...

example : 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 17 1 := by
  ...
```

Prefer also the exact cube identity if it is a one-line regression:

```lean
example : DkMath.CosmicFormulaBinom.GN 3 17 1 = 7 ^ 3 := by
  ...
```

The report must explicitly state:

> A universal cubic GN no-square-lift theorem is false; `(q,u,x) = (7,17,1)` is a certified counterexample.

This is not a failure of GNPC-006. It is one of its central structural results.

---

# 6. Strongly preferred optional theorem — simple-root / derivative nondegeneracy

Only after P0–P6 are complete and clean, expose the simple-root fact behind Hensel lifting.

For

$$
F(u,x)=u^2+3ux+3x^2,
$$

the derivative with respect to `u` is

$$
\partial_uF=2u+3x.
$$

Away from the ramified prime `3`, a prime divisor of a primitive shell should not simultaneously divide this derivative.

Suggested theorem:

```lean
theorem prime_not_dvd_cubic_boundary_derivative
    {q u x : ℕ}
    (hq : Nat.Prime q)
    (hcop : Nat.Coprime u x)
    (hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 u x)
    (hq3 : q ≠ 3) :
    ¬ q ∣ 2 * u + 3 * x := by
  ...
```

A useful identity is

$$
4GN_3(u,x)=(2u+3x)^2+3x^2.
$$

This is the discriminant `-3` completed-square form in the other coordinate direction.

If implemented, this theorem should be described as the local nondegeneracy needed for a future Hensel-lift classification. **Do not implement a full Hensel theorem in GNPC-006.**

---

# 7. Interpretation and relation to FLT3

The module/report should clearly distinguish these statements:

1. Primitive `d = 3` coordinates have a special ramified prime `3`.
2. On primitive coordinates, `3` does not square-lift.
3. Prime divisors away from `3` lie in the `1 mod 3` split sector.
4. Square lifts do exist in that split sector.
5. Therefore a proof strategy that globally assumes `q^2 ∤ GN3` is too strong.
6. A future FLT3-native closure should instead classify which square-lift sectors are compatible with a hypothetical Fermat packet, or absorb them through the Eisenstein norm/unit/descent structure.

Do not state that GNPC-006 itself proves or nearly proves FLT3. It provides the arithmetic classification layer needed to revisit the conditional no-lift gate.

---

# 8. Forbidden scope expansion

Do not implement in GNPC-006:

- changes to `DkMath.FLT.FLT_d3_by_padicValNat`;
- replacement/removal of `hS0_not_sq` or `NoSqOnS0`;
- a full unconditional FLT3 proof;
- full classification of all solutions to `q^2 ∣ GN 3 u x`;
- Hensel lifting modulo arbitrary `q^k`;
- Eisenstein integer PID/UFD redevelopment;
- quadratic reciprocity as a large standalone theory;
- full theorem `p ≡ 1 mod 3 ↔ ∃ u x, GN 3 u x = p`;
- uniqueness/multiplicity of cubic prime representations;
- FLT5 or FLT7 refactoring;
- general odd-prime exponent `d` theory;
- cyclotomic bridge implementation beyond the minimal theorem reuse needed for P3.

GNPC-006 stops at the degree-three prime-divisor sector and square-lift classification above.

---

# 9. Validation

Build at least the final owner module, expected:

```text
lake build DkMath.NumberTheory.GNThreePrimeArithmetic
```

If another owner is selected, build that module instead.

Requirements:

- no new `sorry`;
- no new `axiom`;
- no warning-producing unused theorem arguments;
- imports should remain thin;
- do not import FLT application towers merely to reuse an elementary cubic identity.

---

# 10. Required report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-006.md
```

Include:

1. Outcome A / B / C.
2. Exact existing DkMath gcd/valuation/cubic APIs reused.
3. Exact Mathlib theorem(s) used for the `3 ∣ q - 1` step, including whether the proof used multiplicative order or a cyclotomic theorem.
4. Final owner module and imports.
5. Final theorem types P0–P6.
6. Whether the optional derivative/simple-root theorem was added.
7. Exact regression proving `GN 3 17 1 = 343 = 7^3` and `7^2 ∣ GN 3 17 1`.
8. Explicit statement that universal cubic no-square-lift is false.
9. Build results.
10. Deferred items, especially full Hensel classification and FLT3 reconnection.

---

# 11. Stop condition

STOP when the following structure is formally available and validated:

```text
primitive cubic GN shell
        ↓
3 ∣ GN3  ↔  3 ∣ boundary
        ↓
3^2 ∤ GN3

prime q | GN3, q ≠ 3
        ↓
3 | q - 1

q^2 | GN3
        ↓
q ≠ 3
        ↓
3 | q - 1
```

and the explicit square-lift witness

```text
GN 3 17 1 = 343 = 7^3
```

is recorded.

Do not continue automatically into Hensel lifting or FLT3 proof repair.
