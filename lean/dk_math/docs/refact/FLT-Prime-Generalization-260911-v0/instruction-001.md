# FLT prime-generalization Phase 1 — PrimeAdicPowerSplit

## Goal

Phase 0 established that the front-half arithmetic of the current FLT7 ramified route is not intrinsically degree seven.

This phase promotes the successful generic probe lemmas into production modules and constructs a production `PrimeAdicPowerSplit` normal form for odd prime exponent `p`.

The target is **not** a general FLT theorem and **not** a rewrite of `DkMath.FLT.Seven`.

The target is the following arithmetic statement pattern.

For an odd prime `p`, let

```text
R := GTail p 1 g u
```

and assume

```text
Nat.Prime p
3 ≤ p
0 < g
0 < x
Nat.Coprime g u
p ∣ g
g * R = x ^ p
```

Then produce positive coprime `a,b` such that

```text
g = p ^ (p - 1) * a ^ p
R = p * b ^ p
x = p * a * b
¬ p ∣ b
```

This is the generic odd-prime counterpart of the front half of `SevenAdicPowerSplit`.

---

## Non-goals

Do **not** in this phase:

- modify any file under `DkMath/FLT/Seven/**`;
- import `DkMath.FLT.Seven` into the production generic module;
- generalize `TraceOneInt (-2)`, `sevenAxis`, real-cubic, degree-six, or terminal ramified machinery;
- claim a contradiction or general FLT;
- use `sorry`, `axiom`, or unverified helper assumptions;
- mechanically move all probe declarations into one oversized module.

The purpose is to determine how far the ramified **arithmetic normal form** is genuinely prime-generic before the seven-specific algebraic layer begins.

---

# Part A — Promote the successful probe lemmas

Promote only the reusable content of `DkMathTest.FLT.Prime.GeneralizationProbe`.

The probe file should remain as a regression/test surface, but production code must not depend on `DkMathTest`.

## A1. Boundary gcd corollaries

Preferred home:

```text
DkMath/Lib/Cosmic/GTailBoundary.lean
```

Add production corollaries equivalent to:

```lean
theorem gcd_GN_eq_gcd_of_one_le
    {d g u : ℕ} (hd : 1 ≤ d) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail d 1 g u) = Nat.gcd g d
```

and, if useful for downstream readability, prime branch corollaries:

```lean
theorem gcd_GN_prime_eq_one_of_not_dvd ...
theorem gcd_GN_prime_eq_prime_of_dvd ...
```

Avoid duplicating proofs already contained in `gcd_GTail_eq_gcd_choose`; these should be thin corollaries.

Classification after promotion: `CORE-PROMOTED`.

## A2. Prime divisibility address

Preferred home:

```text
DkMath/Lib/Cosmic/GTailCongruence.lean
```

Promote the exact theorem:

```lean
theorem prime_dvd_GN_iff_dvd_gap
    {p g u : ℕ} (hp : Nat.Prime p) :
    p ∣ GTail p 1 g u ↔ p ∣ g
```

Important: retain the Phase-0 result that this includes `p = 2` and requires no coprimality.

If the proof needs the probe-local prime-row sum helper, promote the smallest reusable helper with a mathematical name and document its scope. Do not expose implementation-only helpers unnecessarily.

Classification: `CORE-PROMOTED`.

## A3. Sharpen the mod-p² convenience API

Current core has a `5 ≤ p` wrapper although the underlying general theorem only needs `2 < p` at `r = 1`.

Add a new production theorem, preferably:

```lean
theorem GN_modEq_head_mod_sq_of_odd_prime_dvd_x
    {p : ℕ} (g u : ℕ)
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpg : p ∣ g) :
    GTail p 1 g u ≡ p * u ^ (p - 1) [MOD p ^ 2]
```

Do not break existing callers of the current `5 ≤ p` theorem. Keep it as a compatibility/thin wrapper if necessary.

Classification: `CORE-PROMOTED`.

## A4. Exact odd-prime residual valuation

Preferred home:

```text
DkMath/Lib/Cosmic/GTailPadic.lean
```

Promote:

```lean
theorem padicValNat_GN_prime_eq_one_of_dvd_gap
    {p g u : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    padicValNat p (GTail p 1 g u) = 1
```

Also consider a direct corollary:

```lean
¬ p ^ 2 ∣ GTail p 1 g u
```

under the same assumptions, because Phase 1 needs the stripped residual to be prime-to-`p`.

Preserve the documented boundary counterexample:

```text
GTail 2 1 2 1 = 4
padicValNat 2 4 = 2
```

Do not weaken the odd-prime boundary without a new Lean proof.

Classification: `CORE-PROMOTED`, with `p = 2` explicitly `PGEN-BOUNDARY` for exact depth one.

## A5. Generic coprime power-factor split

The theorem

```lean
theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d)
```

is not FLT-specific.

Place it in an appropriate low-level number-theory module. Reuse Mathlib's `exists_eq_pow_of_mul_eq_pow`; do not build a new unique-factorization proof.

If an existing DkMath generic theorem already has the same contract, reuse it instead of adding another alias.

Classification: `CORE-PROMOTED` or `CORE-ALREADY`.

## A6. Generic valuation conservation

Preferred home:

```text
DkMath/Lib/NumberTheory/PadicValNat.lean
```

Promote the Probe F/G content with names not tied to FLT7:

```lean
theorem padicValNat_carrier_shape_of_mul_eq_prime ... :
  ∃ m, padicValNat p carrier = (p - 1) + p * m
```

and

```lean
theorem prime_pow_sub_one_dvd_carrier ... :
  p ^ (p - 1) ∣ carrier
```

Record explicitly that these valuation-conservation results themselves also hold at `p = 2`; the odd-prime restriction enters from the residual exact-depth theorem, not from valuation conservation.

Classification: `CORE-PROMOTED`.

---

# Part B — Production generic packet

Create a production module, suggested path:

```text
DkMath/FLT/Prime/AdicPowerSplit.lean
```

It may depend on the promoted Lib theorems, but it must not depend on `DkMath.FLT.Seven`.

## B1. Input packet

Define a small structure or theorem contract representing the arithmetic ramified input. Suggested structure:

```lean
structure PrimeAdicFactorPacket (p g u x : ℕ) : Prop where
  prime : Nat.Prime p
  odd : 3 ≤ p
  gap_pos : 0 < g
  distinguished_pos : 0 < x
  coprime_gap_unit : Nat.Coprime g u
  prime_dvd_gap : p ∣ g
  factor_eq : g * GTail p 1 g u = x ^ p
```

Names may be adjusted to repository conventions, but keep the contract minimal.

Do not include consequences such as `p ∣ residual`, `p ∣ x`, gcd, or valuations as fields; derive them.

## B2. Immediate generic consequences

For a packet `P`, prove:

```text
p ∣ GTail p 1 g u
Nat.gcd g (GTail p 1 g u) = p
padicValNat p (GTail p 1 g u) = 1
¬ p^2 ∣ GTail p 1 g u
p ∣ x
```

The `p ∣ x` proof should come from `p ∣ x^p` and primality; do not assume it as packet data.

## B3. Strip the unique common p layer

Let

```text
c := g / p
r := GTail p 1 g u / p
d := x / p
```

Establish exact reconstruction:

```text
g = p * c
GTail p 1 g u = p * r
x = p * d
```

and prove:

```text
Nat.Coprime c r
¬ p ∣ r
Nat.Coprime (p ^ 2 * c) r
```

For `Nat.Coprime c r`, prefer the standard gcd-division theorem using the already proved exact gcd `= p`.

For `¬ p ∣ r`, derive it from exact valuation one / no `p²` residual rather than a special seven argument.

## B4. Normalized p-th-power product

Prove:

```lean
(p ^ 2 * c) * r = (p * d) ^ p
```

or an equivalent form directly equal to `x ^ p`.

This is the generic form of the current FLT7 normalized product before `seventh_power_factor_split`.

## B5. Split the coprime factors

Apply the generic power-factor split to obtain:

```text
p^2 * c = A^p
r = b^p
```

Then use primality to obtain `p ∣ A`; write

```text
A = p * a.
```

The critical exponent arithmetic to certify is:

```text
p^2 * c = (p*a)^p
=> c = p^(p-2) * a^p
=> g = p^(p-1) * a^p.
```

Do this with explicit natural-exponent identities. The hypothesis `3 ≤ p` ensures the `p - 2` and `p - 1` decompositions are legitimate. Avoid informal cancellation hidden behind arithmetic automation if a small helper theorem makes the exponent accounting clearer.

Then derive:

```text
GTail p 1 g u = p * b^p.
```

## B6. Reconstruct the distinguished factor

From the original product equality and the two normal forms prove:

```text
x ^ p = (p * a * b) ^ p
```

and then, since `p ≠ 0`, use the natural-power injectivity theorem to conclude:

```text
x = p * a * b.
```

Do not use an unproved root extraction principle.

## B7. Coprimality and residual prime exclusion

Prove:

```text
Nat.Coprime a b
¬ p ∣ b
```

For coprimality, descend from the stripped-factor coprimality / p-th-power coprimality. Reuse Mathlib `Nat.coprime_pow_*` lemmas if available.

For `¬ p ∣ b`, use `r = b^p` together with `¬ p ∣ r`.

## B8. Output structure

Define the generic output normal form, suggested shape:

```lean
structure PrimeAdicPowerSplit (p g u x : ℕ) : Type where
  input : PrimeAdicFactorPacket p g u x
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  gap_eq : g = p ^ (p - 1) * a ^ p
  residual_eq : GTail p 1 g u = p * b ^ p
  distinguished_eq : x = p * a * b
  prime_not_dvd_b : ¬ p ∣ b
```

If storing `input` creates awkward universe/Prop-to-Type friction, keep the packet external and return an existential theorem first. The mathematical fields above are the required payload.

Prove existence:

```lean
nonempty_primeAdicPowerSplit_of_packet
```

and optionally provide a `Classical.choice` constructor, following the existing FLT7 style.

---

# Part C — p=7 compatibility test, without modifying FLT7

Add a test module, suggested path:

```text
DkMathTest/FLT/Prime/AdicPowerSplitCompatibility.lean
```

This test may import both the new generic module and existing FLT7 modules.

Show that a `SevenAdicCounterexamplePacket` supplies the generic packet hypotheses with

```text
p = 7
g = z - y
u = y
x = x
```

and that the generic split produces the same **shape** as the existing `SevenAdicPowerSplit`:

```text
z - y = 7^6 * a^7
GN/GTail residual = 7 * b^7
x = 7 * a * b
Nat.Coprime a b
¬ 7 ∣ b
```

Do not require proof that the witnesses `a,b` are definitionally equal to the witnesses chosen by the old `Classical.choice` construction. Shape equivalence is sufficient.

This compatibility test is the evidence that Phase 1 really subsumes the arithmetic front half of FLT7.

---

# Part D — Generalization status update

Update or append a report:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-001.md
```

The report must classify each promoted theorem and each `PrimeAdicPowerSplit` step as one of:

- `PGEN-GREEN`
- `PGEN-ASSUMPTION`
- `PGEN-BOUNDARY`
- `PGEN-MISSING-CORE`
- `PGEN-FALSE`
- `P7-STRUCTURAL`

Record the **minimal assumptions Lean actually needs**, especially whether `3 ≤ p`, positivity, or coprimality are used at each step.

If a theorem compiles under weaker assumptions than requested, report that explicitly rather than artificially retaining stronger assumptions.

---

# Required builds

At minimum run:

```bash
lake build DkMath.Lib.Cosmic.GTailBoundary
lake build DkMath.Lib.Cosmic.GTailCongruence
lake build DkMath.Lib.Cosmic.GTailPadic
lake build DkMath.Lib.NumberTheory.PadicValNat
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.GeneralizationProbe
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility
lake build DkMath.FLT.Seven
```

If a facade such as `DkMath.FLT.Prime` is added, build it too.

Run `#print axioms` for the main promoted theorems and the final generic split existence theorem. The expected accepted surface is the ordinary project surface (`propext`, `Classical.choice`, `Quot.sound` as needed). No `sorryAx`.

---

# Stop conditions

Stop Phase 1 and report rather than forcing the proof if any of the following occurs:

1. Exact residual valuation one needs genuinely seven-specific algebra after all.
2. The normalized p-th-power split fails for some odd prime.
3. The exponent accounting forces an assumption stronger than odd primality.
4. `Nat.Coprime a b` cannot be recovered without adding an extra input hypothesis.
5. The p=7 compatibility shape cannot be recovered from the existing `SevenAdicCounterexamplePacket`.

A stop is a useful result: it identifies the first genuine seven-specific frontier.

---

# Success criterion

Phase 1 is successful if Lean certifies a production theorem/structure equivalent to

```text
odd prime p
+ primitive gap/unit
+ p | gap
+ gap * GTail(p,1,gap,unit) = distinguished^p

=>

gap = p^(p-1) * a^p
GTail(p,1,gap,unit) = p * b^p
distinguished = p*a*b
Coprime a b
p ∤ b
```

and the p=7 compatibility test reproduces the existing FLT7 ramified arithmetic normal form without importing seven-specific algebra into the generic production module.

If this is GREEN, the next phase is to inspect what remains downstream of `SevenAdicPowerSplit` and mark the exact point at which `TraceOneInt (-2)`, real cubic structure, degree six, or other genuinely seven-specific machinery becomes unavoidable.