# PRIM-L027 — Repaired Four-Seat Clique Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib pinned at v4.32.2. Do not upgrade.

## 0. Purpose

PRIM-L026 is accepted as **Outcome B — PROVED DIAMOND OBSTRUCTION / EXCEPTIONAL COLLISION**.

L026 proved that the fourth seat `6*k+2` creates a genuine A/D collision, always sharing old prime `2`, with all common old-prime support localized to `{2,3}`. Keep that module and theorem surface unchanged.

The next checkpoint remains in **Lean-judgment mode**. Do not perform a report-only reconnaissance.

Repair the fourth seat by shifting it one unit:

```text
anchor n = 4*k
A = 2*k
B = 2*k+1
C = 6*k+1
D' = 6*k+3
```

The working conjecture is that the four complete square points are pairwise coprime under the elementary periodic condition

```text
Nat.Coprime (4*k+3) 15
```

with `0 < k`.

This is deliberately weaker and more arithmetic than a new primality assumption. Lean must decide every edge. If any proposed complete coprimality statement is false, keep the true subset and produce an explicit counterexample/local obstruction instead.

## 1. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/CenteredPacketClique4.lean
```

Prefer:

```lean
import DkMath.NumberTheory.Legendre.CenteredPacketDiamond
```

if that gives the needed L025/L026 API transitively. Keep imports minimal.

Add the new module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify existing L025/L026 theorem statements merely to make the new proof easier. A stronger replacement theorem may be added in the new module and may reuse old theorems as corollaries, but do not refactor old modules in this checkpoint unless a tiny cleanup is unavoidable.

Do not add graph/coloring abstractions.

## 2. L027-1 — repaired fourth-seat shell membership

For `0 < k`, prove:

```lean
SquareOffset (4*k) (6*k+3)
```

This is the actual repaired fourth seat `D'`.

## 3. L027-2 — strengthen A/C if Lean permits

The existing L025 theorem proves A/C coprimality under `Nat.Prime (4*k+1)`. Test the stronger statement without that prime hypothesis:

```lean
Nat.Coprime
  ((4*k)^2 + 2*k)
  ((4*k)^2 + (6*k+1))
```

for arbitrary `k` (or `0 < k` if convenient).

Useful exact arithmetic:

```text
Cpoint = Apoint + (4*k+1)
2*Apoint + (4*k+1) = (4*k+1)*(8*k) + 1
```

Any common divisor of Apoint and `4*k+1` should therefore divide `1`.

Do not assume this prose argument is sufficient. Lean must prove the theorem.

If successful, expose a clearly named stronger theorem. Do not delete the old prime-hypothesis theorem.

## 4. L027-3 — C/D' coprimality

Prove complete-point coprimality of

```text
Cpoint  = (4*k)^2 + (6*k+1)
D'point = (4*k)^2 + (6*k+3)
```

The difference is `2`, while both complete points are odd. Use a direct `Nat.Coprime` argument; do not invoke prime factorization machinery unnecessarily.

Required result:

```lean
Nat.Coprime Cpoint D'point
```

with the weakest honest hypotheses.

## 5. L027-4 — B/D' coprimality

Prove complete-point coprimality of

```text
Bpoint  = (4*k)^2 + (2*k+1)
D'point = (4*k)^2 + (6*k+3)
```

Their difference is

```text
4*k+2 = 2*(2*k+1).
```

A useful exact identity is:

```text
Bpoint = (2*k+1)*(8*k-3) + 4
```

for positive `k` (or use an equivalent Nat-safe identity avoiding subtraction if easier).

A common prime divisor should either be `2` or divide `2*k+1`; `Bpoint` is odd, and the latter branch should reduce to a divisor of `4`.

Lean must prove the complete coprimality theorem; do not stop at old-support disjointness.

## 6. L027-5 — A/D' exceptional constant reduction

Let

```text
Apoint  = (4*k)^2 + 2*k
D'point = (4*k)^2 + (6*k+3)
g       = 4*k+3.
```

First prove that any common prime divisor of Apoint and D'point divides `15`.

Useful Nat-safe identity to test:

```text
2*Apoint + 5*g = g*(8*k) + 15.
```

Since `D'point = Apoint + g`, a common divisor divides both Apoint and g, hence the displayed identity should force divisibility of `15`.

Expose a theorem at the actual old-prime or prime-divisor level, for example:

```text
Nat.Prime q ->
q ∣ Apoint ->
q ∣ D'point ->
q ∣ 15
```

or the strongest thin equivalent Lean naturally supports.

Then use

```lean
hcop15 : Nat.Coprime (4*k+3) 15
```

to prove the required complete coprimality:

```lean
Nat.Coprime Apoint D'point
```

Do not replace `hcop15` by a primality assumption on `4*k+3`.

## 7. L027-6 — four complete points pairwise coprime

Combine:

```text
A/B  existing consecutive edge
B/C  existing packet edge
A/C  strengthened edge from L027-2
C/D' L027-3
B/D' L027-4
A/D' L027-5 under hcop15
```

and expose one theorem stating that A/B/C/D' complete points are pairwise coprime under:

```text
0 < k
Nat.Coprime (4*k+3) 15
```

Do not require `Nat.Prime (4*k+1)` unless Lean proves that it is genuinely necessary. The checkpoint specifically tests whether that earlier hypothesis can be removed from this repaired configuration.

Then derive pairwise disjointness of the four actual

```lean
squareOffsetPrimeSupport (4*k) ...
```

Finsets. Reuse `disjoint_squareOffsetPrimeSupport_of_coprime_points` from L025.

Keep the representation simple; conjunctions are acceptable. Do not introduce a generic clique structure.

## 8. L027-7 — full-cover four-distinct-witness consumer

Consume:

```lean
hfull : SquareOffsetsFullyCovered (4*k)
```

and prove a theorem giving four **pairwise-distinct actual old-prime witnesses** for A/B/C/D'.

The mathematical content must be equivalent to:

```text
∃ pA pB pC pD,
  all six pairwise inequalities among pA,pB,pC,pD
  and
  pA ∈ support A
  pB ∈ support B
  pC ∈ support C
  pD ∈ support D'.
```

Use existing `squareOffsetCovered_iff_primeSupport_nonempty` and the proved support disjointness. Do not reprove coverage semantics.

If thin, derive:

```text
4 ≤ (primeScalesUpTo (4*k)).card
```

as a secondary consequence.

## 9. L027-8 — periodicity / infinitude judgment without analytic number theory

The condition

```text
Nat.Coprime (4*k+3) 15
```

is intended to be an elementary periodic condition, not a hidden prime-distribution hypothesis.

Do not add analytic prime-counting or Dirichlet theorems.

If thin in Nat modular arithmetic, prove at least one explicit infinite arithmetic subfamily of `k` satisfying the condition, e.g. a formula `k = 15*t + c` for a suitable fixed `c`, with `0 < k`, such that Lean proves

```text
Nat.Coprime (4*k+3) 15.
```

Choose `c` only after checking the arithmetic. This theorem is useful only to show that the repaired K4 hypothesis is available on an unbounded elementary family; it still does not imply a contradiction with full cover.

If this creates disproportionate boilerplate, record the exact residue classes in the report and keep L027-8 non-public.

## 10. Mandatory stronger-beam judgment

After the four-distinct-witness theorem builds, test whether the repaired configuration gives anything beyond a constant four-witness requirement.

In particular, inspect concrete theorem attempts for:

1. a fifth seat that preserves pairwise complete-point coprimality under only finitely many fixed small-prime exclusions;
2. a parameterized family whose number of pairwise-disjoint seats grows with a parameter;
3. a lower bound on required distinct old-prime witnesses that grows faster than the available old-prime directions;
4. a strict incidence deficit under `SquareOffsetsFullyCovered`.

Do not introduce a generic graph framework just to phrase the search.

A fifth-seat candidate is useful only if its six/further new edges can be judged by explicit arithmetic identities. If the first natural candidate fails, record the exact common-prime obstruction rather than forcing the construction.

Stop after this judgment. Do not automatically start PRIM-L028.

## 11. Outcome classification

### Outcome A — DIRECT GROWING MULTI-SEAT LEVERAGE

Use only if the repaired four-seat theorem extends to a genuinely growing family/count deficit or gives an unbounded-family full-cover obstruction.

### Outcome B+ — PROVED FOUR-SEAT CLIQUE / LIGHTWEIGHT PERIODIC FAMILY

Use if Lean proves all four complete points are pairwise coprime under only `Nat.Coprime (4*k+3) 15`, full cover forces four pairwise-distinct witnesses, and the condition is available on an elementary unbounded periodic family, but no growing witness lower bound follows.

### Outcome B — PROVED FOUR-SEAT LOCAL REFINEMENT

Use if the four-seat theorem is true but requires stronger/local hypotheses or does not admit the lightweight periodic interpretation.

### Outcome C — REPAIR FAILS

Use if one of the required edges is false or the proposed `15` reduction does not produce complete coprimality under `hcop15`.

## 12. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-repaired-four-seat-clique-lean-judgment-260825.md
```

The report must record:

- every declaration added;
- whether A/C became unconditional;
- exact C/D' and B/D' proofs;
- exact A/D' common-divisor reduction;
- whether `Nat.Coprime (4*k+3) 15` sufficed;
- four-way pairwise coprimality/support disjointness;
- full-cover four-distinct-witness theorem;
- any `4 ≤ card` consequence;
- periodic/unbounded-subfamily result if implemented;
- stronger-beam judgment;
- final Outcome A/B+/B/C and stop boundary.

## 13. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketClique4
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Run the existing trailing-whitespace and forbidden-placeholder audits.

Do not upgrade Mathlib. Do not perform a full repository build unless unexpectedly required by a dependency change.

## 14. Non-goals

Do not:

- prove or claim Legendre's conjecture;
- use twin-prime or Dirichlet assumptions;
- add analytic prime-counting;
- hide a prime assumption inside a new predicate;
- erase or rewrite the L026 exceptional-collision theorem;
- add graph/coloring/matching infrastructure;
- return to report-only reconnaissance;
- start PRIM-L028 automatically.

The essential Lean judgment is:

```text
L026 showed the naive fourth seat collides on {2,3}.
Shift D by +1.
        ↓
Test whether the collision collapses to the fixed constant 15.
        ↓
Nat.Coprime (4*k+3) 15
        ↓ ?
Four complete square points pairwise coprime
        ↓ ?
full cover -> four pairwise-distinct old-prime witnesses
        ↓
judge whether this can begin a genuinely growing family.
```
