# Codex Instruction — PRIM-L003 Square-Anchor Residue Cover

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-047 is complete.

The generic finite-prime-world stack now includes:

```text
SupportDisjointFrom
primeScalesUpTo
primeWorldModulus
primeWorldResidues
fresh-prime refinement
q - 1 survivor cardinality
global no-collision refinement
exact canonical residue refinement
finite product formula
Euler totient identification
```

The current Legendre application already contains:

```text
SquareCell
SquareOffset
squareCell_iff_exists_squareOffset
LegendreConjecture
SquareAnchoredSupportEscape
squareAnchoredSupportEscape_iff_raw
prime_of_squareAnchoredSupportEscape
legendreConjecture_of_squareAnchoredSupportEscape
legendreConjecture_iff_squareAnchoredSupportEscape
```

Thus the application already has the square shell, the support-free-point primality closure, and the exact conjecture/provider equivalence.

The missing roadmap layer is PRIM-L003: explicitly expose the finite residue-cover structure of the square anchor `n^2`.

This checkpoint is a semantic localization/rewrite layer only.  It must **not** prove the universal escape provider.

---

# Goal

For offsets `r` in the square shell

```text
1 <= r <= 2*n
```

make explicit that an old prime direction `q <= n` forbids `r` exactly when

```text
q ∣ n^2 + r
```

and package the union of those forbidden waves as a finite cover predicate/set.

Then prove that

```text
SupportDisjointFrom (primeScalesUpTo n) (n^2 + r)
```

is exactly the statement that `r` is not covered by any old prime wave.

Finally rewrite `SquareAnchoredSupportEscape` as a finite square-offset cover-failure statement:

```text
for every n > 0,
not all offsets 1..2*n are covered.
```

This is the exact local combinatorial frontier.  Do not prove that such an uncovered offset exists beyond rewriting the already-defined provider.

---

# Preferred ownership

Keep this in the Legendre application layer, not in the generic Primitive core.

Preferred implementation location:

```text
DkMath/NumberTheory/Legendre.lean
```

because `SquareOffset` and `SquareAnchoredSupportEscape` already live there and moving them would create unnecessary refactoring.

If the file becomes materially too large, a sibling application module is acceptable, but avoid import cycles and do not move existing declarations merely for aesthetics.

Do not add Legendre dependencies to `DkMath.NumberTheory.Primitive`.

---

# Required reconnaissance

Before coding, inspect current Mathlib APIs for:

```text
Nat.ModEq
Nat.modEq_zero_iff_dvd
Nat.add_mod
Nat.mod_eq_zero_of_dvd
Finset.Icc
Finset.mem_Icc
Finset.filter
```

and any current theorem that cleanly expresses the additive inverse residue of `n^2` modulo `q` in `Nat`.

Do not assume an old theorem name.

For the modular forbidden-residue theorem, prefer a robust subtraction-safe formulation over forcing an awkward natural-number `-n^2` expression.

---

# Required implementation surface

Names below are preferred but not mandatory.  Report the final names.

## 1. Prime-wave prohibition predicate

Add a minimal semantic predicate:

```lean
def SquareOffsetForbiddenBy (n q r : ℕ) : Prop :=
  q ∣ n ^ 2 + r
```

This definition intentionally does not require `q` to be prime.  Primality/boundedness belongs to the covering quantifier below.

A simp theorem exposing the definition is welcome if useful, but do not create alias noise.

## 2. Covered-by-old-prime-world predicate

Add:

```lean
def SquareOffsetCovered (n r : ℕ) : Prop :=
  ∃ q, q ∈ primeScalesUpTo n ∧ SquareOffsetForbiddenBy n q r
```

Equivalent binder forms are fine.

Prove the raw prime form:

```lean
theorem squareOffsetCovered_iff_exists_prime_dvd
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      ∃ q, Nat.Prime q ∧ q ≤ n ∧ q ∣ n ^ 2 + r
```

This should be a thin use of `mem_primeScalesUpTo`.

## 3. Support-disjointness = not covered

This is the core semantic bridge.

Prove:

```lean
theorem supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered
    {n r : ℕ} :
    SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) ↔
      ¬ SquareOffsetCovered n r
```

Preferred proof route:

```text
SupportDisjointFrom primeScalesUpTo
  ↔ no prime q <= n divides n^2+r
  ↔ no covering q exists
```

Reuse the existing support semantics.  Do not re-prove prime-divisor facts.

No `SquareOffset n r` hypothesis is required for this equivalence; keep it globally reusable if the proof is clean.

## 4. One-prime forbidden residue / modular phase

Expose that a fixed prime wave forbids one residue class of `r` modulo `q`.

At minimum, prove a `Nat.ModEq` form equivalent to:

```text
q ∣ n^2 + r
iff
n^2 + r ≡ 0 [MOD q]
```

but preferably expose the actual offset phase as well.

A suggested canonical Nat residue helper is:

```lean
def squareAnchorForbiddenResidue (n q : ℕ) : ℕ :=
  (q - (n ^ 2 % q)) % q
```

and, for `0 < q`, a target theorem of the form:

```lean
theorem squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
    {n q r : ℕ} (hq : 0 < q) :
    SquareOffsetForbiddenBy n q r ↔
      r % q = squareAnchorForbiddenResidue n q
```

Equivalent formulations are acceptable if they are simpler in current Mathlib, for example a `Nat.ModEq` theorem expressing that `r` is the additive inverse phase of `n^2` modulo `q`.

Important requirements:

- avoid incorrect use of truncated natural subtraction;
- handle the case `n^2 % q = 0` correctly;
- do not introduce an integer-modulo framework solely for this theorem unless genuinely necessary;
- do not build a new modular arithmetic abstraction layer.

If the exact canonical-residue helper creates disproportionate friction, keep a clean `Nat.ModEq` formulation and report why.

## 5. Finite square-offset set

Package the shell offsets as a finite set:

```lean
def squareOffsets (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 (2 * n)
```

Prove:

```lean
@[simp] theorem mem_squareOffsets
    {n r : ℕ} :
    r ∈ squareOffsets n ↔ SquareOffset n r
```

Reuse the existing `SquareOffset` definition.

## 6. Covered and escaping finite offset sets

Add finite observer sets, preferably:

```lean
def coveredSquareOffsets (n : ℕ) : Finset ℕ :=
  (squareOffsets n).filter (SquareOffsetCovered n)


def escapingSquareOffsets (n : ℕ) : Finset ℕ :=
  (squareOffsets n).filter (fun r => ¬ SquareOffsetCovered n r)
```

Prove exact memberships:

```lean
@[simp] theorem mem_coveredSquareOffsets ... :
  r ∈ coveredSquareOffsets n ↔
    SquareOffset n r ∧ SquareOffsetCovered n r

@[simp] theorem mem_escapingSquareOffsets ... :
  r ∈ escapingSquareOffsets n ↔
    SquareOffset n r ∧ ¬ SquareOffsetCovered n r
```

Then connect escaping membership directly to the existing support predicate:

```lean
theorem mem_escapingSquareOffsets_iff_supportDisjointFrom
    {n r : ℕ} :
    r ∈ escapingSquareOffsets n ↔
      SquareOffset n r ∧
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)
```

This theorem is one of the main deliverables.

## 7. Full-cover predicate

Add a semantic proposition for the bad local event:

```lean
def SquareOffsetsFullyCovered (n : ℕ) : Prop :=
  ∀ r, SquareOffset n r → SquareOffsetCovered n r
```

A finite-set equality characterization is encouraged:

```lean
theorem squareOffsetsFullyCovered_iff_coveredSquareOffsets_eq
    {n : ℕ} :
    SquareOffsetsFullyCovered n ↔
      coveredSquareOffsets n = squareOffsets n
```

or an equivalent theorem.

Likewise expose:

```lean
theorem not_squareOffsetsFullyCovered_iff_escaping_nonempty
    {n : ℕ} :
    ¬ SquareOffsetsFullyCovered n ↔
      (escapingSquareOffsets n).Nonempty
```

if this is clean.

The intent is to make the obstruction literally a finite covering problem.

## 8. Exact provider rewrite — main application theorem

Prove an exact reformulation of the existing provider:

```lean
theorem squareAnchoredSupportEscape_iff_not_fully_covered :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n
```

Also acceptable / encouraged:

```lean
theorem squareAnchoredSupportEscape_iff_escapingSquareOffsets_nonempty :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n → (escapingSquareOffsets n).Nonempty
```

At least one of these must be present; both are preferred if the second is a thin corollary.

This theorem must be a **rewrite of the existing provider**, not a proof of it.

## 9. Optional exact Legendre cover frontier

If very thin, combine the already-proved

```text
legendreConjecture_iff_squareAnchoredSupportEscape
```

with the new rewrite to expose:

```lean
theorem legendreConjecture_iff_squareOffsets_not_fully_covered :
    LegendreConjecture ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n
```

This is allowed because it is only theorem composition.

Do not turn this into a new proof attempt.

---

# Mathematical interpretation to preserve in docstrings

State clearly:

- for fixed anchor `n`, every old prime `q <= n` reserves one modular phase of the offset coordinate `r`;
- `SquareOffsetCovered n r` means at least one old prime wave hits `n^2 + r`;
- `SupportDisjointFrom (primeScalesUpTo n) (n^2+r)` is exactly failure of that union cover at `r`;
- the Legendre-equivalent provider is therefore the assertion that the finite interval `1..2n` is never completely covered by those square-anchored prime waves;
- the generic PHZ / prime-world results established earlier concern global periodic residue spaces, while this checkpoint exposes the **local square-anchored window** that remains hard;
- no counting/density fact currently implies this local escape automatically.

This distinction is essential.

---

# Non-goals

Do **not** add in PRIM-L003:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of `LegendreConjecture`;
- a union-bound/cardinality argument claiming global residue abundance forces a local survivor;
- prime density / PNT / Bertrand / Nagura / known Legendre-strength external prime-gap theorems;
- new PHZ periods or residue enumerations;
- Euler-totient estimates;
- recursive sieve machinery;
- RH / CFBRC dependencies;
- ABC / FLT dependencies;
- category theory;
- a new CRT/modulo abstraction framework;
- a claim that every uncovered residue is globally prime without the existing square-Body bound hypotheses.

Do not hide the conjecture-equivalent existence statement inside a helper assumption.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

If a new sibling Legendre module is created, build it explicitly as well.

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report existing unrelated occurrences separately; do not broaden scope.

---

# Acceptance criteria

PRIM-L003 is complete when:

1. a fixed old prime wave has an explicit square-offset prohibition predicate;
2. the union cover over `primeScalesUpTo n` is exposed;
3. support-disjointness of `n^2+r` is exactly equivalent to offset non-coverage;
4. a fixed `q` prohibition is connected to a modular residue/phase statement without Nat-subtraction errors;
5. `1..2n` is represented as a finite offset set and exactly matches `SquareOffset`;
6. covered and escaping finite offset sets have exact membership theorems;
7. the bad event "all square offsets are covered" is explicitly represented;
8. `SquareAnchoredSupportEscape` is exactly rewritten as failure of full coverage / nonemptiness of the escaping set for every positive `n`;
9. no universal escape, Legendre proof, density argument, or external prime-gap theorem is introduced;
10. builds and audits are clean.

---

# Mandatory stop after PRIM-L003

Stop after this checkpoint.

The roadmap's intended mandatory review point after the Legendre reduction is now reached because L001, L002, and L004 were already implemented before this missing L003 layer.

Do not begin a provider proof in the same pass.

The next review must classify what the completed theory actually supplies against the local cover frontier:

```text
global periodic residue abundance
exact finite-world refinement
Euler/totient cardinality
square-anchor modular phases
finite-prime escape APIs
Primitive Origin / Depth / Mass assets
```

and identify which of these, if any, yields genuinely new information about:

```text
Can the old-prime forbidden phases cover every r in 1..2n?
```

That question is the next research frontier, not part of PRIM-L003.
