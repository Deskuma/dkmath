# Codex Instruction — PRIM-047 Euler Totient Bridge

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-046 is complete.

The current canonical finite-world residue API includes:

```text
primeWorldModulus
primeWorldResidues
mem_primeWorldResidues
mem_primeWorldResidues_iff_supportDisjointFrom
refinedSurvivingSeats_primeWorldResidues_eq
card_primeWorldResidues_insert
card_primeWorldResidues_eq_prod_sub_one
card_primeWorldResidues_primeScalesUpTo
```

For every certified finite prime world `S`:

```text
(primeWorldResidues S).card = ∏ p ∈ S, (p - 1)
```

This product formula was derived internally from the DkMath refinement mechanism:

```text
old canonical residue
  -> q children
  -> exactly one reserved by fresh q
  -> q - 1 survivors
  -> exact global refinement
  -> finite-set induction
```

Euler's totient function has deliberately not been used so far.

This checkpoint now connects the completed DkMath finite-world theory to the standard mathematical name/API.

---

# Goal

Add a thin bridge between:

```text
primeWorldResidues S
```

and Mathlib's Euler totient function `Nat.totient`.

The intended mathematical statement is:

```text
|primeWorldResidues S| = φ(primeWorldModulus S)
```

and, for `KnownPrimeScales S`, combine this identification with the already-proved DkMath product formula to obtain:

```text
φ(primeWorldModulus S) = ∏ p ∈ S, (p - 1)
```

Crucial proof direction:

**Do not prove the DkMath product formula from Mathlib's totient multiplicativity or squarefree formula.**

The DkMath product formula already exists independently.  PRIM-047 is a bridge / identification layer only.

---

# Preferred module

Create:

```text
DkMath/NumberTheory/Primitive/EulerTotientBridge.lean
```

Import only the generic Primitive modules needed, preferably:

```text
DkMath.NumberTheory.Primitive.PrimeWorldCardinality
```

plus the minimal Mathlib totient import required by the current Lean 4.32 / Mathlib API.

Update:

```text
DkMath/NumberTheory/Primitive.lean
```

to publicly import the new bridge.

Keep `PHZ30` concrete facts out of the generic bridge unless a tiny corollary is clearly useful and does not introduce dependency inversion.

---

# Required reconnaissance

Before coding, inspect the current Mathlib API for Euler totient.

Search / `#check` at least:

```text
Nat.totient
Nat.totient_def
Nat.card_coprime
Nat.Coprime
```

and search for lemmas characterizing `Nat.totient n` as the cardinality of numbers below `n` coprime to `n`.

Do not assume theorem names from older Mathlib versions.

The preferred proof should reuse Mathlib's definition/cardinality characterization directly.  If `Nat.totient` is definitionally the relevant filtered range, a short `simp` / unfolding proof is ideal.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final declaration names.

## 1. Cardinality = totient bridge

Prove, preferably **without** `KnownPrimeScales`:

```lean
theorem card_primeWorldResidues_eq_totient
    (S : Finset ℕ) :
    (primeWorldResidues S).card =
      Nat.totient (primeWorldModulus S)
```

Why no prime-world hypothesis should be needed:

`primeWorldResidues S` is defined directly as the residues below `primeWorldModulus S` that are coprime to that modulus.  Euler's totient counts exactly the same finite object.

If the current Mathlib definition/API forces a small syntactic bridge such as coprimality symmetry, use it explicitly.

Do not route this through the product formula.

This theorem is an identification of two cardinality definitions, not a prime-factor theorem.

## 2. Totient product formula for a certified finite prime world

Using **only** the bridge above plus the already-established DkMath theorem

```text
card_primeWorldResidues_eq_prod_sub_one
```

prove:

```lean
theorem totient_primeWorldModulus_eq_prod_sub_one
    {S : Finset ℕ}
    (hS : KnownPrimeScales S) :
    Nat.totient (primeWorldModulus S) =
      ∏ p ∈ S, (p - 1)
```

The intended proof shape is conceptually:

```text
Nat.totient (primeWorldModulus S)
  = (primeWorldResidues S).card
  = ∏ p ∈ S, (p - 1)
```

Do not use Mathlib's Euler-product / multiplicativity theorem to prove this result.

This theorem should visibly certify that the product formula was derived on the DkMath side first and is merely being identified with `Nat.totient` now.

## 3. Canonical bounded-world wrapper

Add:

```lean
theorem totient_primeWorldModulus_primeScalesUpTo (P : ℕ) :
    Nat.totient (primeWorldModulus (primeScalesUpTo P)) =
      ∏ p ∈ primeScalesUpTo P, (p - 1)
```

as a thin specialization using:

```text
knownPrimeScales_primeScalesUpTo
```

Do not re-prove anything about bounded primes.

## 4. Optional refinement recurrence in totient vocabulary

If it is a very thin corollary, expose:

```lean
theorem totient_primeWorldModulus_insert
    {S : Finset ℕ}
    (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    Nat.totient (primeWorldModulus (insert q S)) =
      Nat.totient (primeWorldModulus S) * (q - 1)
```

Preferred proof: rewrite both totients through `card_primeWorldResidues_eq_totient` and reuse `card_primeWorldResidues_insert`.

Again: do not invoke Mathlib totient multiplicativity as the engine.

This corollary is optional if it creates unnecessary rewriting friction.

---

# Concrete PHZ corollaries — optional and secondary

Only if they are essentially free after the generic bridge, one or both of the following may be added in `PHZ30.lean` or another concrete location:

```lean
Nat.totient 30 = 8
Nat.totient 210 = 48
```

Prefer deriving them through the already-established PHZ / prime-world cardinality facts rather than `norm_num` alone, so the connection remains visible.

Do not enumerate the 48 residues.

These concrete certificates are not required for acceptance of PRIM-047.

---

# Mathematical interpretation to preserve in docstrings

State clearly:

- `primeWorldResidues S` is DkMath's canonical finite reduced-residue space for the modulus `primeWorldModulus S`.
- `Nat.totient` gives the standard cardinality name for that same coprime residue space.
- `card_primeWorldResidues_eq_prod_sub_one` was already proved from DkMath refinement before this bridge.
- PRIM-047 identifies the DkMath count with Euler's totient; it does not use Euler's totient to justify the earlier refinement theory.
- residue-space membership is still not a primality assertion.

---

# Non-goals

Do **not** add in PRIM-047:

- a new proof of Euler totient multiplicativity;
- a new proof of the general prime-power totient formula;
- a new squarefree arithmetic framework;
- Möbius inversion;
- prime density / Mertens / PNT;
- PHZ210 residue enumeration;
- recursive sieve machinery beyond existing finite-world refinement;
- Legendre provider work;
- RH / CFBRC dependencies;
- category theory.

Do not replace the DkMath product proof with an appeal to Mathlib's totient formula.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Primitive.EulerTotientBridge
lake build DkMath.NumberTheory.Primitive.PrimeWorldCardinality
lake build DkMath.NumberTheory.Primitive.PrimeWorldResidues
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report any existing unrelated occurrence separately; do not broaden scope to repair unrelated modules.

---

# Acceptance criteria

PRIM-047 is complete when:

1. `primeWorldResidues` cardinality is identified with `Nat.totient` at the same modulus;
2. the theorem does not require `KnownPrimeScales` unless current Mathlib semantics genuinely force it;
3. the certified finite-world totient product formula is obtained by composing the bridge with the already-proved DkMath product formula;
4. no Mathlib totient multiplicativity/squarefree theorem is used as a replacement proof engine;
5. the canonical `primeScalesUpTo` wrapper is available;
6. `Primitive.lean` exports the new bridge;
7. all requested builds and audits are clean.

Stop after PRIM-047.  Do not begin the next Legendre/provider checkpoint in this implementation pass.

---

# Likely next checkpoint after review

If PRIM-047 closes cleanly, review the completed finite-world stack before returning to Legendre:

```text
support semantics
  -> periodic modulus
  -> mirror symmetry
  -> concrete PHZ30
  -> fresh-prime refinement
  -> q-1 survivor cardinality
  -> global no-collision refinement
  -> exact canonical residue refinement
  -> finite product formula
  -> Euler totient identification
```

The next mathematically interesting step should then be chosen between:

```text
PRIM-048A  finite-world density ratio / exact survivor fraction
PRIM-048B  square-cell localization of canonical residue seats
PRIM-048C  return to Legendre SquareAnchoredSupportEscape frontier
```

Do not choose or implement that next step inside PRIM-047.
