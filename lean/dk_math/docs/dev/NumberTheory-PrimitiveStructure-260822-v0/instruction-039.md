# PRIM-L024 — Centered-Pair Common-Support Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep the current Lean / Mathlib v4.32.2 setup unchanged.

## 0. Purpose

This checkpoint changes the working mode.

The recent PAR / L023 / FD / JAC / QR / ST checkpoints were reconnaissance-heavy.  From this checkpoint onward, use Lean as the arbiter: formulate a small exact arithmetic claim, prove it in Lean, and only then judge whether it gives genuine leverage on the Legendre full-cover frontier.

This is **not** a report-only checkpoint.

Do not attempt a proof of Legendre's conjecture.  Do not add `sorry`, axioms, or speculative theorem statements whose truth is unknown.  If a proposed consumer statement is false or cannot be justified from the proved API, stop and document that boundary instead of weakening hypotheses silently.

## 1. Mathematical target

For `0 ≤ j < n`, pair the two shell offsets around the half-integer center:

```text
leftOffset  = n - j
rightOffset = n + 1 + j
```

Both lie in `1 .. 2*n`, and their square-shell points are

```text
L = n^2 + (n - j)
R = n^2 + (n + 1 + j).
```

The exact difference is

```text
R = L + (2*j + 1).
```

Hence any prime dividing both centered points must divide the small odd gap `2*j+1`.

This is different from the existing packet pairing `r ↔ n+r`, whose difference is the anchor `n` and whose coprimality is controlled by `Nat.Coprime n r`.

The purpose of PRIM-L024 is to let Lean decide whether this second exact pairing yields a new common-support restriction that can actually be consumed by the current full-cover frontier.

## 2. Ownership / module

Preferred new module:

```text
DkMath/NumberTheory/Legendre/CenteredPair.lean
```

Use existing public APIs from `Basic`, `Wave`, `CoprimePacket`, `PacketCoprimality`, and `Frontier` as needed.  Keep dependencies one-way and thin.  Do not move existing declarations.

If the theorem surface is genuinely useful, add the module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not change unrelated modules.

## 3. Required proof-backed core

Implement the smallest useful definitions if they improve statements:

```lean
def centeredLeftOffset (n j : ℕ) : ℕ := n - j

def centeredRightOffset (n j : ℕ) : ℕ := n + 1 + j
```

Names may be adjusted if an existing naming convention is better.

Then prove Lean theorems equivalent in content to the following.

### L024-1: both centered offsets are in the shell

For `j < n`:

```text
SquareOffset n (n-j)
SquareOffset n (n+1+j)
```

### L024-2: exact centered point difference

For `j < n`:

```text
n^2 + (n+1+j)
  = (n^2 + (n-j)) + (2*j+1).
```

Do this over `Nat` without introducing integer subtraction.

### L024-3: exact common-divisor reduction

For positive `q` (or with the weakest hypotheses actually required), prove the exact equivalence

```text
q ∣ n^2 + (n-j)
∧ q ∣ n^2 + (n+1+j)

↔

q ∣ n^2 + (n-j)
∧ q ∣ (2*j+1).
```

The theorem should be a direct consequence of L024-2 plus divisibility arithmetic.  Avoid rebuilding a second modular-wave theory.

### L024-4: old-prime common-support characterization

Using `squareOffsetPrimeSupport`, package L024-3 into an exact theorem of the form

```text
q ∈ squareOffsetPrimeSupport n (n-j)
∧ q ∈ squareOffsetPrimeSupport n (n+1+j)

↔

Nat.Prime q
∧ q ≤ n
∧ q ∣ n^2 + (n-j)
∧ q ∣ (2*j+1).
```

Equivalent association/order of conjunctions is fine.

### L024-5: disjoint-support corollary for a large prime gap

If

```text
Nat.Prime (2*j+1)
n < 2*j+1
j < n,
```

prove that the two old-prime support Finsets are disjoint.

Mathematical reason: any common old prime `q ≤ n` dividing the prime gap `2*j+1` would have to equal that gap, contradicting `q ≤ n < 2*j+1`.

Prefer a theorem about `Disjoint` Finsets or an equivalent empty intersection statement.

### L024-6: full-cover consumer theorem

Use the actual full-cover API.  Under `SquareOffsetsFullyCovered n`, `j<n`, and the L024-5 prime-gap hypotheses, derive that the two centered seats admit **distinct** old-prime witnesses.

A target shape is conceptually:

```text
∃ p q,
  p ≠ q
  ∧ p ∈ squareOffsetPrimeSupport n (n-j)
  ∧ q ∈ squareOffsetPrimeSupport n (n+1+j)
```

Use existing `squareOffsetCovered_iff_primeSupport_nonempty` or the current frontier API rather than reproving coverage semantics.

This theorem is required because the checkpoint must reach an actual consumer of the full-cover hypothesis, not stop at a standalone gcd identity.

## 4. Lean-judgment gate

After L024-1 through L024-6 build, test whether this centered pairing gives information **strictly beyond** the existing packet coprimality layer.

Inspect at least these two questions in code/theorem terms:

1. Can the centered-pair distinct-witness theorem be combined with the packet pairing to force a three-seat or four-seat witness condition not already implied by `PacketCoprimality` / `PacketCross`?
2. Does summing or organizing the centered-pair common-support restriction produce a new finite inequality under `SquareOffsetsFullyCovered n` that is not merely another restatement of exact wave spacing?

Do **not** invent a theorem statement merely to obtain Outcome A.

If a stronger consumer theorem is found and Lean proves it, add it with a narrow statement and explain exactly why it is new.

If no stronger consumer follows, stop after the proved core and classify the route honestly as structural-only.

## 5. True / False discipline

Use two beams explicitly.

### True beam

Only claims that Lean proves without new assumptions become library theorems.

### False / insufficient beam

If an attractive strengthening fails because it is false, produce a small explicit arithmetic counterexample when practical and prove that counterexample in Lean (`norm_num`, `decide`, or elementary arithmetic as appropriate).  If the issue is not falsity but simply missing implication, document the exact missing hypothesis/theorem in the report; do not encode an artificial axiom or provider.

## 6. Expected classification

After the Lean implementation, write:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-centered-pair-lean-judgment-260825.md
```

Classify one of:

```text
Outcome A — DIRECT FULL-COVER LEVERAGE
  Lean proves a genuinely stronger full-cover restriction/inequality that was
  unavailable from the packet/wave APIs.

Outcome B — PROVED STRUCTURAL REFINEMENT
  The centered common-support theorems are valid and reusable, but the only
  full-cover consumer is a distinct-witness/repackaging result with no new
  obstruction.

Outcome C — REDUNDANT WITH EXISTING WAVE/PACKET API
  Even the proof-backed centered formulation adds no meaningful theorem surface.
```

## 7. Stop boundary

Do not start PRIM-L025 automatically.

Stop after:

1. the Lean theorem core is implemented,
2. the relevant module/facade build passes,
3. the proof-backed report is written,
4. Outcome A/B/C is assigned.

The next checkpoint will be chosen from the proved Lean facts, not from reconnaissance alone.
