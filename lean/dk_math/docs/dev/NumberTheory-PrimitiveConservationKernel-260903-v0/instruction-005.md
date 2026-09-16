# PCK-003 — Coarse-to-fine square certification implementation instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-004.md` / PCK-002G

## 0. Authorization

Implement exactly the first thin coarse-to-fine primality-certification adapter.

PCK-003 must compose only already-established APIs:

```text
q ≤ P
  ↓
squareBody q ≤ squareBody P        -- PCK-002: squareBody_mono
  ↓
m ≤ squareBody P
  ↓
SupportDisjointFrom (primeScalesUpTo P) m
  ↓
Nat.Prime m                        -- existing SquareBody certification
```

Do not introduce a new complete-prime-set definition. PCK-000 already established that
`primeScalesUpTo P` is the canonical complete bounded prime support.

Do not implement prime expansion, primorial closure, the 30 → 960 regression,
fresh-prime extraction, or any RH/PHZ consequence in this checkpoint.

## 1. Source of truth

Inspect the current canonical owner before editing:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Required existing declarations include:

```lean
def squareBody (P : ℕ) : ℕ

theorem squareBody_mono {q P : ℕ} (h : q ≤ P) :
    squareBody q ≤ squareBody P

theorem prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
    {P m : ℕ}
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody P)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    Nat.Prime m
```

Also reuse the existing semantics in `FinitePrimeWorld.lean`:

```lean
mem_primeScalesUpTo
supportDisjointFrom_primeScalesUpTo_iff
```

Do not re-prove any of these.

## 2. Required theorem

Add one public theorem in namespace:

```text
DkMath.NumberTheory.Primitive
```

Preferred semantic shape:

```lean
/--
A complete prime support at a coarse anchor `P` certifies every fine
square-Body world whose anchor `q` satisfies `q ≤ P`.
-/
theorem prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
    {q P m : ℕ}
    (hqP : q ≤ P)
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody q)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    Nat.Prime m := by
  ...
```

The exact theorem name may be shortened if current local naming conventions strongly favor another form, but the roles `q = fine anchor` and `P = coarse complete-support anchor` must remain obvious from the docstring and argument names.

The proof should be the transparent two-step composition:

```lean
have hmUpperCoarse : m ≤ squareBody P :=
  hmUpper.trans (squareBody_mono hqP)

exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
  hm hmUpperCoarse hdisj
```

Equivalent `exact` / `apply` style is acceptable.

## 3. Mathematical meaning

This theorem formalizes:

$$
q\le P,
\qquad
1<m\le q(q+2),
$$

and absence of every prime divisor at most `P` imply that `m` is prime.

The key point is not a new primality criterion. It is the reuse law:

> one complete coarse prime world at anchor `P` certifies every finer square world `q ≤ P`.

Equivalently,

$$
\operatorname{squareBody}(q)
\subseteq
\operatorname{squareBody}(P)
$$

at the order level, so the coarse prime support is sufficient for the entire nested family.

This is the arithmetic bridge needed later for the statement that one primorial coarse anchor can govern all intermediate fine square anchors after its complete prime closure is known.

## 4. Canonical support firewall

Do not add:

```text
PrimeCompleteUpTo
CompletePrimeBasis
CoarsePrimeWorld
FinePrimeWorld
```

or any equivalent new wrapper.

The canonical complete support remains:

```lean
primeScalesUpTo P
```

with exact membership:

```lean
q ∈ primeScalesUpTo P ↔ Nat.Prime q ∧ q ≤ P
```

PCK-003 is only a theorem adapter.

## 5. Gnomon / half-unit firewall

PCK-003 must not import or depend on:

```text
DkMath.CosmicFormula.SquareGnomon
DkMath.CosmicFormula.HalfUnitZeroConjugate
```

Those are geometric/algebraic layers. The current theorem is purely natural-number order plus finite prime support.

The later campaign may connect the layers semantically, but dependency direction should remain minimal.

## 6. Optional raw-support wrapper

Do not add a second theorem using the raw condition

```lean
∀ ⦃p : ℕ⦄, Nat.Prime p → p ≤ P → ¬ p ∣ m
```

unless source inspection shows a strong existing naming symmetry that makes the omission awkward.

The preferred PCK-003 public surface is the canonical `SupportDisjointFrom (primeScalesUpTo P) m` theorem only.

If a raw-condition wrapper is added, justify why it is not redundant in `report-005.md`.

## 7. No-go items

PCK-003 must not:

- change `squareBody_mono`;
- change any existing SquareBody theorem statement;
- add new definitions or structures;
- implement square prime expansion;
- implement fresh-prime existence or a new FreshPrimeDirection theorem;
- import PrimorialUniverse;
- add the numeric `30 → 960` regression;
- add Gnomon resolution/projective theorems;
- add RH, zeta, Xi, PHZ, CFBRC, or analytic dependencies;
- add `sorry`, `admit`, `native_decide`, or a project axiom;
- modify public aggregators for this one wrapper.

## 8. Expected proof footprint

The new theorem should be very small. A large proof is a warning that the adapter is being overdesigned.

Expected load-bearing reuse:

```text
squareBody_mono
prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
```

No factorization, minFac, wheel, CRT, or GN reasoning should be needed.

## 9. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Primitive.SquareBody
git diff --check
```

Run:

```lean
#print axioms DkMath.NumberTheory.Primitive.<final_theorem_name>
```

Audit the modified source for newly introduced forbidden constructs.

## 10. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-005.md
```

Record:

- Outcome
- branch and starting HEAD
- changed files
- exact final theorem name and statement
- exact proof composition
- why `primeScalesUpTo P` is reused instead of a new complete-support wrapper
- focused build result
- `git diff --check`
- axiom/sorry audit
- whether any optional raw wrapper was added
- deferred frontier
- next authorization

## 11. Next authorization

If PCK-003 is green, authorize only the next existing roadmap checkpoint:

> PCK-004 — square escape → fresh prime direction, using the already-existing
> SquareBody / FreshPrimeDirection surface and adding only the smallest missing
> semantic bridge if one is genuinely absent.

Do not implement PCK-004 in this checkpoint.
