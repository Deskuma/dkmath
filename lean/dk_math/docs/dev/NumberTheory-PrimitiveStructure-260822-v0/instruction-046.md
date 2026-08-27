# PRIM-L031 — Fresh-Collision Matching / Consecutive Small-Cofactor Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Review decision carried into this checkpoint

PRIM-L030 is accepted as **Outcome A — EXACT FRESH-COLLISION GCD CHARACTERIZATION**.

The important theorem surface now available is:

```text
old-support disjointness for two distinct shell seats
  iff
complete-point gcd = 1
  or
complete-point gcd is one prime q with n < q.
```

The gcd also divides the ordered offset gap, and the gap is strictly smaller than
`2*n`.

Do not weaken this back to complete-point coprimality.  The concrete witness
`n=3`, offsets `1,6`, with `gcd(10,15)=5>3`, must remain a valid fresh-collision
example.

This checkpoint must now determine what the nontrivial fresh branch actually looks
like geometrically inside one square shell.

## 1. Purpose

Let

```text
A = n^2 + r
B = n^2 + s
```

with `r<s`, both offsets in the square shell, and assume their actual old-prime
supports are disjoint but `gcd A B != 1`.

L030 gives

```text
q := gcd A B
Prime q
n < q
q | (s-r)
0 < s-r < 2*n.
```

Because `n<q`, one also has `2*n < 2*q`.  Therefore the positive multiple
`s-r` of `q` cannot be `2*q` or larger.  The expected exact conclusion is:

```text
s - r = q.
```

Then, because `q | A` and `B=A+q`, the two complete points should have the form

```text
A = q * k
B = q * (k+1)
```

with a bounded consecutive cofactor pair

```text
0 < k
k + 1 <= n.
```

The checkpoint must prove or refute this in Lean, and then determine whether such
fresh collisions form a genuine matching: one shell seat should not be able to
participate in two different nontrivial fresh collisions.

This is a proof-backed implementation checkpoint.  Do not replace theorem attempts
with report-only reconnaissance.

## 2. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/FreshCollisionMatching.lean
```

Suggested imports:

```text
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.SmallCofactor
```

Use fewer imports if possible.

Add the module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify the public statements of L022 or L025--L030.
Do not introduce a general graph library.
Do not use analytic prime distribution.

At most one small local/public predicate for a fresh-collision pair is allowed if it
substantially shortens the theorem statements.

## 3. L031-1 — nontrivial fresh gcd equals the seat gap

For

```text
hr   : SquareOffset n r
hs   : SquareOffset n s
hrs  : r < s
hdisj : Disjoint (squareOffsetPrimeSupport n r)
                  (squareOffsetPrimeSupport n s)
hg1  : Nat.gcd (n^2+r) (n^2+s) != 1
```

let

```text
q := Nat.gcd (n^2+r) (n^2+s).
```

Reuse L030 to obtain `Prime q` and `n<q`.

Prove the exact gap theorem:

```text
s - r = q.
```

A suggested name is:

```lean
freshCollision_gcd_eq_orderedOffsetGap
```

or an equivalent readable name.

The proof should reuse:

```text
gcd_squarePoints_dvd_orderedOffsetGap
prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
```

and a finite divisibility argument.  Do not reprove the full L030 classification.

Also derive the useful location consequences:

```text
r < n
n < s
```

if they are true under the same hypotheses.  The intended meaning is that every
nontrivial fresh collision crosses from the lower half of the offset window to the
upper half.

If either inequality is false, retain the exact counterexample in Lean and adjust
the later matching statement accordingly.

## 4. L031-2 — consecutive small-cofactor factorization

Under the same hypotheses, prove an existential factorization of the form:

```text
exists k,
  0 < k
  and k + 1 <= n
  and q * k = n^2 + r
  and q * (k+1) = n^2 + s.
```

Orientation of the multiplication equality may follow existing style.

The mathematical route should be finite and elementary:

1. `q | n^2+r` because `q` is the gcd;
2. write `n^2+r = q*k`;
3. use `s-r=q` to obtain the second factorization;
4. use the strict square-shell upper bound
   `n^2+s < (n+1)^2` together with `n<q` to prove `k+1<=n`.

Do not use real division or logarithms.

If convenient, expose a thin theorem saying the two cofactors are consecutive and
bounded; do not introduce a new cofactor structure unless repeated fields make it
clearly worthwhile.

The concrete L029/L030 witness must specialize to:

```text
n = 3
r = 1
s = 6
q = 5
k = 2
k+1 = 3.
```

Add a tiny `norm_num`/reuse sanity theorem only if it is useful for confirming the
general statement and does not bloat the public API.

## 5. L031-3 — the fresh prime is unique at each shell point

Test and prove the following local uniqueness statement if true:

```text
SquareOffset n r
Prime q1
Prime q2
n < q1
n < q2
q1 | n^2+r
q2 | n^2+r
--------------------------------
q1 = q2.
```

This should follow because two distinct factors both larger than `n` would have
product at least `(n+1)^2`, while an actual shell point is strictly below
`(n+1)^2`.

Before proving it from scratch, inspect whether the existing generic
unique-fresh-small-split API underlying `SmallCofactor.lean` already yields the
same fact with less duplication.  Prefer a thin specialization if available.

A suggested theorem name is:

```lean
unique_fresh_prime_divisor_of_squareOffset
```

The theorem is about fresh prime divisors of one actual square-shell point; do not
claim uniqueness of all prime divisors.

## 6. L031-4 — fresh collisions form an ordered matching

Using L031-1 and L031-3, prove that a lower seat cannot have two different fresh
collision partners.

A target shape is:

```text
fresh collision r--s
fresh collision r--t
--------------------------------
s = t.
```

Likewise prove the upper-end version:

```text
fresh collision r--s
fresh collision t--s
--------------------------------
r = t.
```

The exact predicate may be expanded rather than defined if that is clearer.  A
minimal predicate is acceptable, for example conceptually:

```text
FreshCollisionPair n r s :=
  SquareOffset n r /
  SquareOffset n s /
  r < s /
  Disjoint (support r) (support s) /
  gcd(point r, point s) != 1.
```

Do not create generic graph/matching infrastructure.  The required content is only
endpoint uniqueness for this arithmetic relation.

If L031-1 proves `r<n<s`, record that this orientation is canonical: a seat cannot
serve as a lower endpoint of one fresh collision and an upper endpoint of another.
Together with endpoint uniqueness, this is the precise sense in which fresh
collisions form a matching.

## 7. L031-5 — old support lives entirely in the consecutive cofactors

For the factorization

```text
n^2+r = q*k
n^2+s = q*(k+1)
q > n
```

prove, or reuse existing theorems to show, that bounded old primes cannot be supplied
by `q` and therefore come entirely from `k` and `k+1`.

At minimum prove membership equivalences for bounded primes:

```text
p in squareOffsetPrimeSupport n r
  iff
Prime p and p <= n and p | k

p in squareOffsetPrimeSupport n s
  iff
Prime p and p <= n and p | k+1.
```

If a more canonical existing `PrimeScaleGeneratedBy` / `SmallCofactor` theorem gives
the same information, use it instead of duplicating definitions.

Also record, if cheap, that the positive bounded cofactors are generated by the old
prime world:

```text
PrimeScaleGeneratedBy (primeScalesUpTo n) k
PrimeScaleGeneratedBy (primeScalesUpTo n) (k+1).
```

Do not claim they are prime.

## 8. L031-6 — full-cover consequence

Now consume

```text
hfull : SquareOffsetsFullyCovered n.
```

For a nontrivial fresh collision pair, use the factorization above and the fact that
both shell seats are covered to prove that both bounded cofactors carry actual old
prime content.

A useful target is:

```text
2 <= k
k + 1 <= n
```

with explicit nonempty old support for each of `k` and `k+1` expressed in the
existing vocabulary where possible.

The first inequality may be obtained by reusing
`two_le_smallCofactor_of_covered_fresh_split` if its hypotheses fit naturally;
otherwise prove the thin contradiction directly (`k=1` would make the first point
a fresh prime with no old support).

The mathematical interpretation to preserve is:

```text
fresh collision under full cover
  -> one fresh q > n shared by two seats
  -> consecutive bounded cofactors k, k+1
  -> each seat's old cover must be paid entirely inside those cofactors.
```

## 9. L031-7 — mandatory descent / stronger-beam judgment

After the exact matching/cofactor theorems build, make one concrete Lean attempt to
see whether this produces a genuine smaller-state descent.

Do **not** call the existence of `k<n` a descent by itself.
A valid descent result would need something of the form:

```text
fresh-collision/full-cover state at n
  -> reconstructed Legendre obstruction or full-cover state at m<n
```

with the relevant hypotheses preserved.

If that cannot be proved, state this explicitly in the report and stop the descent
claim.

Also judge whether the matching theorem gives any strictly stronger capacity
inequality than L029.  Endpoint uniqueness alone is not a new capacity breaker.

Do not introduce a selector, maximum matching, graph coloring, Hall theorem, or
analytic counting merely to force an Outcome A.

## 10. Outcome classification

### Outcome A — FRESH-COLLISION DESCENT / NEW CAPACITY LEVERAGE

Use only if Lean proves the matching/cofactor normalization **and** one genuinely
stronger frontier-relevant theorem, such as:

- a strict smaller Legendre/full-cover state with preserved hypotheses; or
- a new capacity inequality not already equivalent to L029.

### Outcome B — EXACT FRESH-COLLISION MATCHING STRUCTURE

Use if Lean proves the expected exact geometry:

```text
gap = fresh gcd q
points = q*k and q*(k+1)
q unique per point
fresh collisions form a matching
old support transfers to the bounded cofactors
```

but no descent or stronger capacity obstruction follows.

This is still a useful proof-backed structural result.

### Outcome C — PROPOSED FRESH-COLLISION NORMAL FORM FAILS

Use if a central proposed statement is false, especially:

- `gap = q`;
- bounded consecutive cofactors;
- unique fresh prime per shell point; or
- endpoint uniqueness.

In that case, preserve a minimal Lean counterexample and do not paper over the
failure with a weaker descriptive wrapper.

## 11. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-fresh-collision-matching-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- proof of `gap = q` or counterexample;
- lower/upper-half location result;
- consecutive cofactor factorization and exact bounds;
- fresh-prime uniqueness proof route;
- endpoint matching result;
- old-support/cofactor transfer;
- full-cover consequence;
- the concrete `n=3, r=1, s=6` specialization;
- the descent attempt and why it succeeds or fails;
- Outcome A/B/C;
- exact stop boundary.

## 12. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.FreshCollisionMatching
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the recent trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib.  Do not run a full repository build unless dependency
changes unexpectedly require it.

## 13. Non-goals

Do not:

- claim Legendre's conjecture;
- treat a smaller integer cofactor as a proved descent without reconstructing the
  relevant state;
- introduce general graph/matching infrastructure;
- use PNT, Bertrand, Chebyshev, Rosser--Schoenfeld, Jacobsthal, or sieve estimates;
- erase the fresh `gcd=5` branch by strengthening back to complete coprimality;
- reprove L030 from scratch;
- return to report-only reconnaissance instead of Lean theorem attempts.

The intended arithmetic spine is:

```text
old-support disjoint + nontrivial gcd
        ↓ L030
one fresh prime q > n
        ↓ gcd | seat gap < 2n < 2q
seat gap = q
        ↓
q*k = first square point
q*(k+1) = second square point
        ↓
0 < k < k+1 <= n
        ↓
one fresh q can pair shell seats only once
        ↓
all old-cover information is forced into consecutive bounded cofactors
```
