# PRIM-L025 — Centered/Packet Triangle Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep the repository pinned at Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Purpose

PRIM-L024 is accepted as **Outcome B — PROVED STRUCTURAL REFINEMENT**.

The next checkpoint must continue in **Lean-judgment mode**, not report-only reconnaissance.
Do not create another broad survey. Implement a small concrete synthesis of the proved L020 packet-coprimality layer and the proved L024 centered-pair layer, then let Lean decide exactly how far the synthesis goes.

The target configuration is the three square-shell offsets at anchor `n = 4*k`:

```text
A-offset = 2*k
B-offset = 2*k + 1
C-offset = 6*k + 1
```

For `0 < k`, all three lie in the shell `1 .. 2*(4*k)`.

They are chosen because three different exact mechanisms meet on the same triple:

```text
A <-> B : consecutive complete integers
B <-> C : packet pair with base r = 2*k+1 and gap 4*k
A <-> C : centered pair with j = 2*k and odd gap 4*k+1
```

If `4*k+1` is prime, the centered gap is a prime strictly larger than the anchor.
The aim is to prove, in Lean, whether these three mechanisms really force a three-way pairwise separation and therefore three pairwise-distinct old-prime witnesses under full cover.

This is not a request to prove Legendre's conjecture. It is a request to make the first explicit three-seat synthesis theorem and to stop immediately if it does not scale beyond a local structural refinement.

## 1. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/CenteredPacketTriangle.lean
```

Import only what is needed, preferably:

```lean
import DkMath.NumberTheory.Legendre.CenteredPair
import DkMath.NumberTheory.Legendre.PacketCoprimality
```

If `CenteredPair` already imports enough of `PacketCoprimality`, keep the import surface minimal.

Add the new module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not refactor or rename existing L020/L024 declarations.
Do not introduce a generic graph/coloring framework in this checkpoint.
Do not modify Primitive semantics.

## 2. L025-1 — shell membership of the three seats

For `0 < k`, prove the three offsets are actual `SquareOffset (4*k)` seats:

```text
2*k
2*k+1
6*k+1
```

Use small named lemmas if they improve readability. Avoid a new structure merely to package three naturals.

Expected mathematics:

```text
1 <= 2*k
2*k <= 8*k
1 <= 2*k+1
2*k+1 <= 8*k
1 <= 6*k+1
6*k+1 <= 8*k
```

The last inequality uses `0 < k`.

## 3. L025-2 — consecutive pair A/B

Prove the two complete square points

```text
A = (4*k)^2 + 2*k
B = (4*k)^2 + (2*k+1)
```

are coprime.

The intended proof is the exact consecutive relation `B = A + 1`; use existing `Nat.Coprime` API rather than factorization.

A public theorem should expose the complete-point coprimality, not only support disjointness.

## 4. L025-3 — packet pair B/C

Prove

```text
Nat.Coprime (4*k) (2*k+1)
```

for every natural `k` (or for `0 < k` if that makes the Lean proof materially simpler, though positivity is mathematically unnecessary).

Then reuse the existing theorem

```lean
coprime_squarePacketPoints_of_coprime_offset
```

with

```text
n = 4*k
r = 2*k+1
```

to obtain complete-point coprimality of

```text
B = (4*k)^2 + (2*k+1)
C = (4*k)^2 + (6*k+1).
```

Do not reprove the packet Euclidean argument in this module.

## 5. L025-4 — centered pair A/C

Observe that, at anchor `n = 4*k`, choosing centered index `j = 2*k` gives

```text
centeredLeftOffset  (4*k) (2*k) = 2*k
centeredRightOffset (4*k) (2*k) = 6*k+1
centered gap = 4*k+1.
```

Assume

```lean
hprime : Nat.Prime (4*k+1)
```

and reuse L024 to obtain old-prime support disjointness of A and C.

### Required stronger Lean judgment

Do not stop at support disjointness without testing the stronger complete-point statement.
Attempt to prove:

```text
Nat.Coprime ((4*k)^2 + 2*k)
            ((4*k)^2 + (6*k+1)).
```

under `hprime`.

A useful arithmetic route is:

```text
C = A + (4*k+1).
```

Any common prime divisor therefore divides the prime `4*k+1`. If it were equal to `4*k+1`, show it cannot divide A. One convenient identity to test in Lean is the congruence-level fact encoded by

```text
2*A = 2*(4*k)^2 + 4*k
```

which is congruent to `1` modulo `4*k+1`.

Do not assume this argument works merely from prose. Lean must prove the complete coprimality theorem. If the proposed theorem is false, produce a concrete Lean counterexample/theorem instead and retain only the already-proved old-support disjointness.

## 6. L025-5 — three-way pairwise coprimality / support disjointness

If L025-2, L025-3 and the complete L025-4 strengthening all succeed, expose one theorem stating that the three complete points A, B, C are pairwise coprime, for example as a conjunction of three `Nat.Coprime` propositions.

Then derive pairwise `Disjoint` statements for the three actual old-prime support Finsets:

```text
squareOffsetPrimeSupport (4*k) (2*k)
squareOffsetPrimeSupport (4*k) (2*k+1)
squareOffsetPrimeSupport (4*k) (6*k+1)
```

Prefer deriving support disjointness from complete-point coprimality where possible. Reuse the existing L024 centered support theorem if it keeps the proof thinner.

Do not add an abstract finite-family `Pairwise` framework unless Lean genuinely needs it.

## 7. L025-6 — full-cover three-witness consumer

Now consume the actual frontier hypothesis:

```lean
hfull : SquareOffsetsFullyCovered (4*k)
```

Together with `0 < k` and `Nat.Prime (4*k+1)`, prove a theorem of the form

```text
∃ p q ell,
  p ≠ q ∧
  p ≠ ell ∧
  q ≠ ell ∧
  p ∈ squareOffsetPrimeSupport (4*k) (2*k) ∧
  q ∈ squareOffsetPrimeSupport (4*k) (2*k+1) ∧
  ell ∈ squareOffsetPrimeSupport (4*k) (6*k+1)
```

The exact conjunction nesting may follow Lean style, but the mathematical content must be **three pairwise-distinct actual old-prime witnesses**, not three arbitrary divisors.

Use existing

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

for each seat. Do not reprove coverage semantics.

This theorem is the main required consumer of the checkpoint.

## 8. L025-7 — optional finite-world cardinality consequence

If it is thin after L025-6, prove a necessary cardinality consequence under full cover:

```text
3 <= (primeScalesUpTo (4*k)).card
```

Use the three distinct witnesses and `mem_squareOffsetPrimeSupport`; do not introduce a prime-counting abstraction merely for this result.

This theorem is optional if it creates disproportionate Finset boilerplate. The three-witness theorem is mandatory.

Do not turn the special case `k = 1` into a public Legendre theorem just to manufacture a contradiction. A local numeric sanity example may be placed in the report, but the checkpoint is about the scalable structural statement.

## 9. Stronger-beam judgment — mandatory

After the required theorems build, test whether this triangle gives anything stronger than a constant three-witness requirement.

Specifically inspect, with Lean theorem attempts where there is a concrete statement, whether the same construction yields any of:

1. a family of pairwise-disjoint support seats whose cardinality grows with `k` or `n`;
2. a strict incidence deficit against the available old prime waves;
3. a contradiction with `SquareOffsetsFullyCovered (4*k)` for an unbounded family of `k`;
4. a reusable construction that extends the triangle to four or more pairwise-separated seats without adding an unrelated strong hypothesis.

Do **not** claim any item from arithmetic intuition alone.

If a tempting four-seat extension is false, record a small explicit counterexample and, where convenient, encode the false-beam witness in Lean (`example` or theorem in a clearly non-public/test-local form). Do not bloat the public API with failed conjectures.

The checkpoint must stop after this judgment. Do not automatically start PRIM-L026.

## 10. Outcome classification

Classify the result after Lean has judged the required theorem surface.

### Outcome A — DIRECT MULTI-SEAT LEVERAGE

Use only if the three-seat synthesis scales to a new growing count/deficit or an actual unbounded-family full-cover obstruction.

### Outcome B — PROVED TRIANGLE STRUCTURAL REFINEMENT

Use if Lean proves the three complete points/supports are pairwise separated and full cover forces three distinct witnesses, but no scalable contradiction/count deficit follows.

### Outcome C — NO GENUINE THREE-WAY SYNTHESIS

Use if one of the proposed pairwise relations fails, or the final three-witness theorem collapses to no more than disconnected restatements of the existing pair theorems.

A proved three-witness theorem is normally enough to distinguish B from C even if it does not prove Legendre.

## 11. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-centered-packet-triangle-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- which of the three pair mechanisms proved complete coprimality versus only old-support disjointness;
- the full-cover three-witness theorem;
- any cardinality consequence;
- the mandatory stronger-beam judgment;
- final Outcome A/B/C;
- explicit stop boundary.

Keep module/public theorem docstrings concise and mathematical.

## 12. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketTriangle
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the existing trailing-whitespace / forbidden-placeholder audit used in recent checkpoints.

Do not upgrade Mathlib. Do not perform a full repository build unless a dependency change unexpectedly requires it.

## 13. Non-goals

Do not:

- prove or claim Legendre's conjecture;
- add graph-coloring machinery;
- add asymptotic prime-counting assumptions;
- invoke Jacobsthal bounds;
- revive quadratic-character or shell-transport routes;
- add parity wrappers;
- modify L020/L024 theorem statements merely to make the new proof convenient;
- replace proof with another report-only reconnaissance.

The essential instruction is:

```text
L020 packet coprimality
+ L024 centered support separation
+ consecutive-number coprimality
        ↓
Lean-verified three-seat triangle
        ↓
full cover -> three pairwise-distinct old-prime witnesses
        ↓
judge whether the triangle scales; stop if it does not
```
