# Codex Instruction — GNPC-003 Composite-Degree GN Factorization / Prime-Degree Necessity

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-002 implementation commit:

```text
bdcd8dcfa3174a8561bc1d75260b68db0e2748e1
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-001.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-002.md
lean/dk_math/DkMath/NumberTheory/GNPrimeClosure.lean
lean/dk_math/DkMath/NumberTheory/GNRepresentationBounds.lean
```

---

# 0. Current verified state

GNPC-001 established the prime-product factor-one closure for the canonical GN.

GNPC-002 established the positive representation vocabulary and complete finite search box:

```lean
GNPositiveRepresentation
GNPositiveRepresentation.bounds
GNRepresentationBox
GNPositiveRepresentations
mem_GNPositiveRepresentations_iff
```

In particular, for fixed target `n`, every positive nondegenerate representation

```text
2 ≤ d
0 < x
0 < u
GN d x u = n
```

lies in an explicit finite region.

GNPC-003 now removes all composite degree layers from the prime-target case.

The desired conclusion is:

> In the positive nondegenerate natural-number region, if `GN d x u` is prime,
> then the exponent `d` must itself be prime.

This checkpoint must obtain that conclusion from an internal GN factorization,
not from cyclotomic theory.

---

# 1. Core algebraic identity

For positive boundary `x`, prove the nested composition law

$$
GN_{ab}(x,u)=GN_a(x,u)\,GN_b\!\left(x\,GN_a(x,u),u^a\right).
$$

The intended derivation is from the canonical Cosmic Formula identity

$$
(x+u)^r=x\,GN_r(x,u)+u^r.
$$

Apply it first at exponent `a`:

$$
(x+u)^a=x\,GN_a(x,u)+u^a.
$$

Raise both sides to exponent `b`, then apply the same identity to the new boundary

```text
x * GN a x u
```

and new gap

```text
u ^ a.
```

This yields

$$
(x+u)^{ab}=x\,GN_a(x,u)\,GN_b\!\left(x\,GN_a(x,u),u^a\right)+u^{ab}.
$$

Compare with the direct exponent-`ab` identity

$$
(x+u)^{ab}=x\,GN_{ab}(x,u)+u^{ab}.
$$

Cancel the common `u^(ab)` and then cancel the positive factor `x`.

For this checkpoint, it is acceptable and preferred to state the Nat theorem with
`0 < x`.  Do not force a semiring-polynomial proof merely to eliminate this
hypothesis; all downstream positive representation uses already contain `x > 0`.

Preferred theorem shape:

```lean
theorem GN_mul_degree
    {a b x u : ℕ}
    (hx : 0 < x) :
    DkMath.CosmicFormulaBinom.GN (a * b) x u =
      DkMath.CosmicFormulaBinom.GN a x u *
        DkMath.CosmicFormulaBinom.GN b
          (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a)
```

Equivalent orientation/name is acceptable.  Report the final declaration name.

Before proving it, search the current repository and Mathlib for an exact or
near-exact existing exponent-composition theorem.  Do not duplicate an existing
canonical theorem.

---

# 2. Nontriviality of both nested factors

Assume

```text
2 ≤ a
2 ≤ b
0 < x
0 < u
```

Use GNPC-002 rather than rebuilding positivity from raw sums whenever possible.

The first factor satisfies

$$
GN_a(x,u)\ge 2^a-1\ge3.
$$

For the second factor, its new boundary and gap are positive:

```text
0 < x * GN a x u
0 < u ^ a
```

and therefore

$$
GN_b\!\left(x\,GN_a(x,u),u^a\right)\ge2^b-1\ge3.
$$

Expose either separate reusable lemmas or one packaged theorem proving both
factors are strictly greater than `1`.

Preferred conceptual package:

```lean
theorem one_lt_factors_of_composite_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    1 < DkMath.CosmicFormulaBinom.GN a x u ∧
    1 < DkMath.CosmicFormulaBinom.GN b
      (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a)
```

Do not introduce a general `GN > 1` campaign beyond what is needed here unless a
small reusable theorem falls out naturally.

---

# 3. Composite degree forces composite GN

Combine the composition law with nontriviality of both factors.

Preferred theorem:

```lean
theorem not_prime_GN_of_mul_degree
    {a b x u : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : 0 < x) (hu : 0 < u) :
    ¬ Nat.Prime (DkMath.CosmicFormulaBinom.GN (a * b) x u)
```

Use the canonical Mathlib `Nat.Prime` multiplication API after reconnaissance.
Do not manually reprove elementary primality facts if Mathlib already exposes them.

A direct contradiction through `Nat.prime_mul_iff` is expected to be enough once
the factorization is rewritten.

---

# 4. Prime GN implies prime degree

This is the main theorem of GNPC-003.

Preferred shape:

```lean
theorem prime_degree_of_prime_GN
    {d x u : ℕ}
    (hd : 2 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime d
```

The proof should use the current Mathlib characterization of a nonprime natural
`d ≥ 2` as a product of two factors at least `2`.

Mandatory reconnaissance:

- search Mathlib for the canonical theorem that extracts a nontrivial factorization
  from `¬ Nat.Prime d` under `2 ≤ d`;
- do not guess theorem names;
- if Mathlib gives a divisor rather than an explicit product, derive the factorization
  with the smallest reasonable local argument.

Then substitute `d = a * b` and contradict `not_prime_GN_of_mul_degree`.

The mathematical dependency should be visibly:

```text
composite d
  ↓
d = a*b with a,b ≥ 2
  ↓
GN_ab = GN_a * nested_GN_b
  ↓
both factors > 1
  ↓
GN_d composite
  ↓
contradiction with prime GN
```

---

# 5. Positive representation prime-target wrapper

GNPC-002 already packages the positive representation hypotheses.  Add a thin
wrapper connecting it to the new degree theorem.

Preferred shape:

```lean
theorem GNPositiveRepresentation.degree_prime_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d
```

This theorem should unpack `hrep`, rewrite `GN d x u = p`, and invoke
`prime_degree_of_prime_GN`.

This is the theorem that directly prunes the finite search space from GNPC-002:
for prime target `p`, only prime degree layers remain.

---

# 6. Optional tiny regression checks

If cheap, add lightweight examples such as:

```text
GN 4 1 1 = 15
GN 6 1 1 = 63
```

or examples showing that the composition identity specializes correctly for small
`a,b`.

Keep these lightweight.  Do not build a numerical search campaign in this checkpoint.

---

# 7. Preferred ownership

Create a thin NumberTheory module, for example:

```text
DkMath/NumberTheory/GNDegreeFactorization.lean
```

or another equally clear name.

It may import:

```text
DkMath.NumberTheory.GNRepresentationBounds
```

plus only the minimal Cosmic Formula / Mathlib modules actually needed.

Do not move existing GN declarations.
Do not refactor `CosmicFormulaBinom` or `GTail` globally.

---

# 8. Mandatory report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-003.md
```

Record:

1. exact repository duplicate search result;
2. exact Cosmic Formula identity reused;
3. exact Mathlib composite-number / nontrivial-factorization API reused;
4. final nested GN composition theorem name and type;
5. final composite-degree obstruction theorem;
6. final `prime GN → prime degree` theorem;
7. positive-representation wrapper;
8. build command and result;
9. whether any `sorry` or `axiom` was added;
10. anything deferred.

---

# 9. Explicitly deferred / forbidden expansion

Do **not** continue beyond the degree-primality obstruction in GNPC-003.

Deferred to later checkpoints:

- residue conditions such as `p ≡ 1 [MOD d]`;
- cyclotomic factorization of prime-degree GN;
- classification of `(x,u)` for fixed `(p,d)`;
- uniqueness or multiplicity of GN representations;
- primitive-prime / Zsigmondy theory;
- ABC / FLT / Legendre / RH applications;
- logarithmic optimization of the finite search box;
- arbitrary semiring/polynomial generalization of `GN_mul_degree`;
- Body primality wrappers.

Do not claim that every prime degree produces a prime GN value.
The theorem is only the necessary implication

$$
GN_d(x,u)\text{ prime}\Longrightarrow d\text{ prime}
$$

inside the positive nondegenerate natural-number region.

---

# 10. Validation

At minimum run the focused build for the new module, e.g.

```text
lake build DkMath.NumberTheory.GNDegreeFactorization
```

using the actual final module name.

The checkpoint is complete when the nested composition theorem, composite-degree
obstruction, prime-degree necessity theorem, and positive-representation wrapper
are all present and the focused build succeeds.
