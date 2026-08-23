# Codex Instruction — PRIM-046 Finite Prime-World Product Formula

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-045 is complete.

The canonical finite-world residue API now includes:

```text
primeWorldResidues
mem_primeWorldResidues
mem_primeWorldResidues_iff_supportDisjointFrom
refinedSurvivingSeats_primeWorldResidues_eq
card_primeWorldResidues_insert
```

The key fresh-prime recurrence already proved is:

```text
(primeWorldResidues (insert q S)).card
  = (primeWorldResidues S).card * (q - 1)
```

under:

```text
KnownPrimeScales S
Nat.Prime q
q ∉ S
```

This recurrence was obtained from exact refinement, not from Euler's totient function.

PHZ30/PHZ210 are already identified with canonical residue spaces. In particular:

```text
phzResidues30 = primeWorldResidues primeWorld235
phzResidues210 = primeWorldResidues (insert 7 primeWorld235)
```

and `phzResidues210.card = 48` is already proved without enumerating 48 residues.

User-reported verification for PRIM-045:

```text
lake build DkMath.NumberTheory.Primitive.PrimeWorldResidues
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

No new `sorry`, `admit`, `native_decide`, or `axiom` were introduced.

---

# Goal

Derive the finite prime-world product cardinality formula entirely from the DkMath refinement recurrence:

```text
|primeWorldResidues S| = ∏ p in S, (p - 1).
```

This checkpoint must establish the formula by finite-set induction using `card_primeWorldResidues_insert` as the induction step.

Do **not** use Euler's totient function, Mathlib's totient cardinality formula, reduced-residue cardinality theorems, or a separate analytic/counting argument to prove the main result.

The intended mathematical reading is:

```text
empty prime world: 1 canonical seat
insert fresh prime q: multiply the seat count by q - 1
therefore finite world S: product of all (p - 1)
```

This is the internal DkMath derivation of the multiplicative seat count.

---

# Preferred module

Create:

```text
DkMath/NumberTheory/Primitive/PrimeWorldCardinality.lean
```

Import:

```text
DkMath.NumberTheory.Primitive.PrimeWorldResidues
```

Then add the module to the public aggregator:

```text
DkMath.NumberTheory.Primitive
```

A small implementation inside `PrimeWorldResidues.lean` is acceptable only if a new module would contain essentially no coherent API beyond the main theorem. Prefer the separate module if the base-case and canonical wrappers below are useful.

---

# Required implementation surface

Names are preferred, not mandatory. Report final declaration names.

## 1. Empty-world base certificate

Expose the base case cleanly.

Preferred theorem:

```lean
@[simp] theorem primeWorldResidues_empty :
    primeWorldResidues ∅ = {0}
```

or, if equality is awkward or not useful, at minimum:

```lean
@[simp] theorem card_primeWorldResidues_empty :
    (primeWorldResidues ∅).card = 1
```

Remember:

```text
primeWorldModulus ∅ = 1
```

and the canonical representatives below modulus `1` consist only of `0`; `Nat.Coprime 0 1` holds.

Do not introduce a nonempty-world hypothesis.

## 2. Main finite-world product theorem

Prove:

```lean
theorem card_primeWorldResidues_eq_prod_sub_one
    {S : Finset ℕ}
    (hS : KnownPrimeScales S) :
    (primeWorldResidues S).card =
      ∏ p in S, (p - 1)
```

The exact theorem name may differ, but the statement should remain this direct.

### Required proof architecture

Use `Finset.induction` / `Finset.induction_on` (or an equivalent finite-set induction).

Base:

```text
S = ∅
```

should close from the empty-world residue certificate and the empty product.

Insertion step:

```text
S ↦ insert q S
q ∉ S
```

Given:

```text
KnownPrimeScales (insert q S)
```

extract or derive:

```text
Nat.Prime q
KnownPrimeScales S
```

Then use the existing theorem:

```text
card_primeWorldResidues_insert
```

as the cardinality step:

```text
|R(insert q S)| = |R(S)| * (q - 1)
```

and the induction hypothesis:

```text
|R(S)| = ∏ p in S, (p - 1).
```

Finish with `Finset.prod_insert` and elementary commutativity/associativity as needed.

Do not reprove the child-survivor theorem, exact refinement theorem, or CRT argument in this module.

## 3. Canonical bounded-prime-world wrapper

Add a specialization for the existing canonical constructor:

```lean
theorem card_primeWorldResidues_primeScalesUpTo (P : ℕ) :
    (primeWorldResidues (primeScalesUpTo P)).card =
      ∏ p in primeScalesUpTo P, (p - 1)
```

This should be a thin application of:

```text
knownPrimeScales_primeScalesUpTo
card_primeWorldResidues_eq_prod_sub_one
```

No interval enumeration.

## 4. Optional concrete consistency certificates

If inexpensive, add one or both thin consequences in `PHZ30.lean` or the cardinality module:

```text
(primeWorldResidues primeWorld235).card = 8
(primeWorldResidues (insert 7 primeWorld235)).card = 48
```

They must be derived from the generic product theorem plus the already known concrete world definitions, not from explicit PHZ residue enumeration.

Do not replace the existing `card_phzResidues210` proof unless the replacement is clearly shorter and preserves the constructive refinement story. A separate consistency theorem is sufficient.

---

# Mathematical interpretation to preserve in docstrings

The theorem is a finite prime-direction observer theorem:

```text
one fresh prime direction q
  removes exactly one of q children
  leaves q - 1 children per old canonical seat
```

Iteration over a finite prime world gives:

```text
seatCount(S) = ∏ p in S, (p - 1).
```

This is not yet an Euler-totient theorem in the API, even though the resulting product is the classical squarefree totient product.

Keep the distinction explicit:

```text
DkMath refinement product formula first
Euler φ identification later
```

---

# Explicit non-goals

Do not add in PRIM-046:

- `Nat.totient` / Euler `φ` bridge
- proof of the classical multiplicativity theorem for `φ`
- arbitrary recursive sieve data structures
- ordered prime lists or prime enumeration recursion
- PHZ210 48-residue enumeration
- asymptotic density
- Mertens / PNT / analytic number theory
- Legendre provider or proof
- RH / CFBRC
- category theory

Do not turn the theorem into a primality statement. `primeWorldResidues` remains a finite support/coprimality observer space.

---

# Acceptance checks

Run:

```sh
lake build DkMath.NumberTheory.Primitive.PrimeWorldCardinality
lake build DkMath.NumberTheory.Primitive.PrimeWorldResidues
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

If the theorem is kept inside `PrimeWorldResidues.lean`, omit the nonexistent module build and report that design choice.

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Expected: none.

---

# Stop condition

Stop after the finite product formula, canonical wrapper, and any very small consistency certificates are complete.

Do not proceed to the Euler-φ bridge in this checkpoint.

The next review should decide between:

```text
PRIM-047A  Euler φ identification
PRIM-047B  iterated/canonical prime-stage refinement interface
PRIM-047C  return to the square-window / Legendre application frontier
```
