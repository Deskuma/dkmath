# PRIM-L030 — Old-Support Fresh-Collision GCD Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Review decision carried into this checkpoint

PRIM-L029 is accepted as **Outcome A — STRICTLY WEAKER CAPACITY FRONTIER BRIDGE**.

The strictness witness at `n = 3`, offsets `1` and `6`, is important:

```text
10 and 15 are not coprime,
but their common prime 5 is fresh because 5 > 3,
so the actual old-prime supports are disjoint.
```

The ordered difference theorem also shows that old-support collision is controlled by a small seat gap rather than by the full square-point gcd.

The next checkpoint must stay in Lean-judgment mode and compress this exact phenomenon into a classical gcd criterion.

## 1. Purpose

For two distinct square-shell seats `r` and `s`, let

```text
A = n^2 + r
B = n^2 + s.
```

Because both points share the same square anchor,

```text
gcd(A,B)
```

divides the offset difference `|s-r|`.

Inside the square shell,

```text
1 <= r,s <= 2*n,
r != s,
```

so the nonzero gap is strictly smaller than `2*n`.

If the two actual old-prime supports are disjoint, then no prime `q <= n` can divide the gcd. Since the gcd itself divides a number `< 2*n`, the expected exact classification is:

```text
support-disjoint
  <->
gcd(A,B) = 1
    or
(gcd(A,B) is prime and n < gcd(A,B)).
```

The second branch is exactly a single fresh common-prime collision, as in `gcd(10,15)=5` at `n=3`.

The aim is to prove this classification in Lean and then lift it to the finite-family capacity interface.

## 2. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/OldSupportGcd.lean
```

Import only what is needed, preferably beginning from:

```lean
import DkMath.NumberTheory.Legendre.OldSupportCapacity
```

Add the new module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify L025--L029 theorem statements merely to make this proof convenient.
Do not add a general gcd framework outside Legendre in this checkpoint.
Do not add analytic prime-counting or sieve dependencies.

## 3. L030-1 — pair gcd divides the seat gap

For ordered offsets `r < s`, prove a thin theorem of the form:

```text
Nat.gcd (n^2+r) (n^2+s) | (s-r).
```

Use the shared-anchor identity

```text
n^2+s = (n^2+r) + (s-r).
```

Do not expand squares unnecessarily.

If a symmetric theorem using `Nat.dist r s` is substantially cleaner in Lean, it may be added, but keep the public surface small.

## 4. L030-2 — old-support disjointness as gcd support escape

Prove that two actual support Finsets are disjoint exactly when the gcd has no old-prime support.

Target mathematical content:

```text
Disjoint (squareOffsetPrimeSupport n r)
         (squareOffsetPrimeSupport n s)
<->
SupportDisjointFrom
  (primeScalesUpTo n)
  (Nat.gcd (n^2+r) (n^2+s)).
```

This should be a direct prime-divisor theorem:

```text
q divides both square points
<->
q divides their gcd.
```

Reuse current Primitive support semantics. Do not create a second notion of bounded-prime-free integer.

## 5. L030-3 — optional primorial / finite-world coprimality form

If it is thin using the existing `PeriodicPrimeWorld` theorem surface, prove the equivalent finite-world form:

```text
Disjoint supports
<->
Nat.Coprime
  (Nat.gcd (n^2+r) (n^2+s))
  (primeWorldModulus (primeScalesUpTo n)).
```

Reuse the existing theorem equivalent to

```text
SupportDisjointFrom S m <-> Nat.Coprime m (primeWorldModulus S)
```

with `KnownPrimeScales (primeScalesUpTo n)`.

Do not introduce a new primorial definition.

This target is optional if imports become disproportionate. The fresh-collision classification below is mandatory.

## 6. L030-4 — fresh-collision classification

This is the main Lean judgment.

Assume:

```text
hr : SquareOffset n r
hs : SquareOffset n s
hrs : r != s
```

Attempt to prove the exact theorem:

```text
Disjoint (squareOffsetPrimeSupport n r)
         (squareOffsetPrimeSupport n s)
<->
let g := Nat.gcd (n^2+r) (n^2+s)
  g = 1 or (Nat.Prime g and n < g).
```

Equivalent theorem shape is acceptable if `let` syntax is awkward.

### Forward direction

Use:

1. `g` divides the nonzero seat difference;
2. the seat difference is `< 2*n`;
3. old-support disjointness means every prime divisor of `g` is `> n`;
4. if `g > 1`, choose a prime divisor `p | g`;
5. show a second prime factor or exponent `p^2` would force the gcd above the available gap bound;
6. conclude `g = p`, hence `Nat.Prime g` and `n < g`.

Do not assume this classification from prose. Lean must prove the arithmetic bound.

### Reverse direction

If `g=1`, common old support is impossible.
If `g` is prime and `n<g`, any old prime `q<=n` dividing both square points would divide prime `g`, forcing `q=g`, contradiction.

### Boundary cases

Handle `n=0` and tiny shells honestly. If the theorem naturally needs `0<n`, add exactly that hypothesis and explain why. Do not hide a false endpoint with automation.

If the proposed exact classification is false, produce the smallest concrete Lean counterexample and classify Outcome C. Do not weaken it silently.

## 7. L030-5 — positive fresh-collision theorem

If L030-4 succeeds, expose the nontrivial branch cleanly:

```text
support-disjoint
and
Nat.gcd (n^2+r) (n^2+s) != 1
->
Nat.Prime (Nat.gcd ...)
and
n < Nat.gcd ...
```

Also prove the gap upper bound if thin:

```text
Nat.gcd (...) < 2*n.
```

The mathematical interpretation should be explicit in the docstring:

> the only common factor allowed between two old-support-disjoint shell points is one single fresh prime lying above the old-prime threshold.

## 8. L030-6 — recover the `n=3`, `{1,6}` witness through gcd

Use the new theorem surface to recover the L029 strictness example conceptually:

```text
gcd(10,15)=5,
Nat.Prime 5,
3 < 5.
```

Do not duplicate the entire L029 support proof. This is only a sanity consumer showing that the fresh branch is inhabited.

A local theorem or concise public theorem is acceptable; avoid example namespaces in the production module.

## 9. L030-7 — finite-family gcd interface

If L030-4 succeeds, introduce at most one thin family predicate only if it improves the provider statement. Suggested mathematical form:

```text
GcdFreshSeparatedSquareSeatFamily n R :=
  (forall r in R, SquareOffset n r) and
  forall r in R, forall s in R, r != s ->
    let g := Nat.gcd (n^2+r) (n^2+s)
    g = 1 or (Nat.Prime g and n < g)
```

Then prove equivalence or two-way bridges with:

```text
PairwiseOldSupportDisjointSquareSeatFamily n R.
```

Prefer an equivalence theorem rather than duplicating the capacity proof.

Do not create this predicate if the direct explicit condition is clearer.

## 10. L030-8 — gcd-form capacity / Frontier consumer

If the family bridge is clean, expose a thin theorem saying that a family satisfying the gcd/fresh-collision condition and

```text
(primeScalesUpTo n).card < R.card
```

produces an actual prime in the square cell.

This theorem must be a direct composition through L029. Do not reimplement the finite union counting or Frontier proof.

This target is optional if it would only duplicate a long theorem statement without improving the construction interface.

## 11. Stronger-beam judgment

After the main classification builds, answer the following in the report using the proved theorem surface.

1. Did actual support disjointness become exactly a pairwise gcd condition with only two allowed outcomes: `1` or one fresh prime?
2. Does the family provider problem now avoid explicit support Finsets and bounded-prime quantifiers?
3. Does this reveal a constructive route for growing families, or is it only an exact coordinate compression?
4. Does any stronger claim such as `support-disjoint -> complete coprime` remain false because of the fresh-prime branch?

Do not start a growing-family search in this checkpoint.

## 12. Outcome classification

### Outcome A — EXACT FRESH-COLLISION GCD CHARACTERIZATION

Use if Lean proves the exact two-branch gcd classification and connects it cleanly to the old-support capacity interface.

### Outcome B — GCD SUPPORT-ESCAPE BRIDGE ONLY

Use if Lean proves `support-disjoint <-> bounded-prime-free gcd` / primorial coprimality but the stronger `gcd=1 or one fresh prime` classification does not close.

### Outcome C — FRESH-COLLISION CLASSIFICATION FALSE OR NON-MATERIAL

Use if a genuine counterexample shows the proposed classification is false, or if the gcd layer adds no useful compression over L029.

## 13. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-old-support-gcd-fresh-collision-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- whether ordered or symmetric gcd-gap form was used;
- the support-disjointness/gcd bridge;
- primorial form if implemented;
- exact fresh-collision classification or counterexample;
- `n=3`, `{1,6}` recovery;
- family/provider bridge if implemented;
- Outcome A/B/C;
- explicit stop boundary.

## 14. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.OldSupportGcd
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the recent trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib. Do not perform a full repository build unless a dependency change unexpectedly requires it.

## 15. Non-goals

Do not:

- claim Legendre's conjecture;
- search analytically for large pairwise-separated families;
- add graph/coloring/matching infrastructure;
- revive Jacobsthal or quadratic-character routes;
- duplicate L029 capacity counting;
- erase the fresh common-prime phenomenon by strengthening back to complete coprimality;
- replace the requested Lean theorem attempts with report-only reconnaissance.

The essential checkpoint is:

```text
old-support disjointness
        ↓
common gcd has no old prime factor
        ↓
gcd divides a seat gap < 2*n
        ↓
gcd = 1 or exactly one fresh prime > n
        ↓
finite family condition can be stated purely by gcd/fresh collisions
        ↓
reuse L029 capacity Frontier bridge
```
