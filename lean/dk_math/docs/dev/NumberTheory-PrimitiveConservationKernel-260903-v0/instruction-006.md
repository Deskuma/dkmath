# PCK-004 — Square escape to self-fresh prime direction implementation instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-005.md` / PCK-003

## 0. Authorization

Implement exactly one semantic bridge:

> a nontrivial point that escapes the complete coarse prime support while
> lying in a certified fine square-Body world is itself the fresh prime
> direction.

This checkpoint must not add a new prime-existence mechanism. The repository
already has the generic theorem

```lean
exists_freshPrimeDirection_of_supportDisjointFrom
```

which says that a nontrivial support-disjoint natural has some fresh prime
divisor. PCK-004 is stronger only because square certification from PCK-003
proves that the point itself is prime, so the fresh witness collapses to
`m` itself.

## 1. Reuse inventory

Work in the current canonical owner:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Reuse exactly these established surfaces where possible:

```lean
prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

freshPrimeDirection_of_prime_dvd_not_mem
```

and the existing definitions:

```lean
primeScalesUpTo
SupportDisjointFrom
FreshPrimeDirection
```

Do not re-prove their semantics.

## 2. Required theorem

Add one public theorem in namespace:

```text
DkMath.NumberTheory.Primitive
```

Preferred statement:

```lean
/--
A support-disjoint point in a certified fine square world is not merely
carrying some fresh prime divisor: square certification makes the point
itself prime, hence the point itself is the fresh direction relative to the
complete coarse world.
-/
theorem freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
    {q P m : ℕ}
    (hqP : q ≤ P)
    (hm : 1 < m)
    (hmUpper : m ≤ squareBody q)
    (hdisj : SupportDisjointFrom (primeScalesUpTo P) m) :
    FreshPrimeDirection (primeScalesUpTo P) m m := by
  ...
```

A shorter name is acceptable if it preserves the semantic roles:
- `q` = fine square anchor;
- `P` = coarse complete-prime-support anchor;
- `m` = escaping point and self-witness.

## 3. Expected proof

The proof should be a transparent composition.

First obtain primality from PCK-003:

```lean
have hmPrime : Nat.Prime m :=
  prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
    hqP hm hmUpper hdisj
```

Then obtain absence from the old support by applying support disjointness to
the self-divisibility witness:

```lean
have hmNotMem : m ∉ primeScalesUpTo P :=
  hdisj hmPrime (dvd_refl m)
```

Finally package the self-direction:

```lean
exact freshPrimeDirection_of_prime_dvd_not_mem
  hmPrime (dvd_refl m) hmNotMem
```

Equivalent `dvd_rfl` spelling or direct constructor proof is acceptable,
but prefer reusing the existing constructor theorem if clean.

## 4. Mathematical meaning

PCK-003 already gives

$$
q\le P,
\qquad
1<m\le\operatorname{squareBody}(q),
$$

together with escape from every prime direction at most `P`, implying

$$
m\text{ is prime}.
$$

PCK-004 upgrades the semantic conclusion to

$$
\boxed{
\operatorname{FreshPrimeDirection}
\bigl(
\operatorname{primeScalesUpTo}(P),m,m
\bigr).
}
$$

Because `FreshPrimeDirection S n p` means

$$
p\text{ prime},
\qquad
p\mid n,
\qquad
p\notin S,
$$

the self-witness theorem says:

> inside the certified conservation window, complete-support escape cannot
> remain a composite unresolved point; the escaping point itself becomes the
> new primitive prime direction.

This is the first direct Lean theorem in the PCK campaign matching the
semantic phrase "escape produces a fresh Primitive direction".

Do not generalize this sentence beyond the explicit square-window and
complete-support hypotheses.

## 5. Distinguish from existing generic theorem

The existing

```lean
exists_freshPrimeDirection_of_supportDisjointFrom
```

requires no square bound and concludes only

```lean
∃ p, FreshPrimeDirection S m p
```

for some prime divisor `p`.

PCK-004 must not duplicate or replace it.

The new theorem has a different role:

```text
generic support escape
  -> some fresh prime divisor

complete coarse support + fine square certification
  -> m is prime
  -> fresh direction witness is exactly m
```

Record this distinction explicitly in `report-006.md`.

## 6. Optional conclusions

Do not add a separate theorem concluding `Nat.Prime m`; PCK-003 already owns
that result, and `FreshPrimeDirection ... m m` already contains primality.

Do not add a separate `P < m` theorem in this checkpoint unless Lean proof
engineering unexpectedly requires it. Membership semantics already imply the
fresh point lies outside the complete coarse support.

Do not add existential wrappers.

## 7. Firewalls

PCK-004 must not:

- introduce any new definition or structure;
- add a new factorization/minFac theorem;
- modify `FreshPrimeDirection` or `SupportDisjointFrom`;
- modify PCK-003 certification;
- add prime expansion;
- add primorial/wheel logic;
- add the `30 → 960` regression;
- import SquareGnomon or HalfUnitZeroConjugate;
- add RH, PHZ, zeta, Xi, CFBRC, or analytic dependencies;
- add `sorry`, `admit`, `native_decide`, or a project axiom;
- modify public aggregators.

## 8. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Primitive.SquareBody
git diff --check
```

Run an axiom check on the new theorem:

```lean
#print axioms
  DkMath.NumberTheory.Primitive.<final_theorem_name>
```

Audit the modified source for newly introduced forbidden constructs.

## 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-006.md
```

Record:

- Outcome
- branch and starting HEAD
- changed files
- exact final theorem statement
- exact reuse of PCK-003 certification
- exact reuse of `freshPrimeDirection_of_prime_dvd_not_mem`
- distinction from `exists_freshPrimeDirection_of_supportDisjointFrom`
- why the fresh witness is exactly `m`
- focused build result
- `git diff --check`
- axiom/sorry audit
- next authorization

## 10. Next authorization

If PCK-004 is green, authorize only the next roadmap checkpoint:

> PCK-005 — finite square prime expansion.

PCK-005 should investigate a finite operator that extends a complete prime
world at anchor `P` through the certified square window using old-support
escape, while reusing PCK-003/PCK-004 rather than reimplementing primality.

Do not implement PCK-005 in this checkpoint.
