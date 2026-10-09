# Instruction 003 — Selective GTail transport and conservation certificates

Date: 2026-10-09  
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Working directory: `lean/dk_math`  
Approved prerequisites: `review-001.md`, `review-002.md`, `report-001.md`, `report-002.md`  
Scope: **Step 003 only. Stop before degree-seven factorization or FLT7 bridge.**

## Mission

Implement `DkMath.Lib.Cosmic.GTailTransport` as a neutral algebraic mechanism for **moving selected Pascal terms across the Gap/Body balance** while keeping the Big unchanged. The purpose is "reasoned subtraction": a controlled change of viewing angle, with an exact accounting of moved terms and an explicit separation between **genuine invariants** and **selection-dependent properties**.

This must be a reusable, kernel-checked `CommSemiring` transport layer that builds directly on `GTailSelection` (Step 001) and `GTailFactor` (Step 002). Do not claim gcd, coefficient content, valuation, support, or FLT counterexample properties are universally invariant.

## Phase 0 — inventory

Before coding read:

- `DkMath/Lib/Cosmic/GTailSelection.lean`
- `DkMath/Lib/Cosmic/GTailFactor.lean`
- `DkMath/Lib/Cosmic/GTail.lean` / `GTailPascal.lean`
- focused tests and reports `001`/`002`.

Inspect relevant Mathlib `Finset` identities: intersection, set difference, disjoint unions, sum-sdiff and filter partition. Record exact reused declarations and signatures in `source-inventory-003.md`. Keep existing definitions and import direction.

## Phase 1 — single-term transport over a semiring

For `d k : ℕ`, `S : Finset ℕ`, `x u : R` with `[CommSemiring R]`, and `k ≤ d` with `k ∉ S`, prove both directions of transfer when `k` is inserted into Body:

```text
selectedBody d (insert k S) x u
  = selectedBody d S x u + selectedTerm d k x u

selectedGap d S x u
  = selectedGap d (insert k S) x u + selectedTerm d k x u
```

Provide the symmetric erase operation when `k ∈ S` and `k ≤ d`, either as direct lemmas or via the insert transport.

Cover both no-op cases:

- `k > d`: insertion or erasure does not change the active Body/Gap.
- `k ∈ S`: inserting the same index does not duplicate its term.

No numerical subtraction in the semiring-facing core. If using subtraction, separately add a `CommRing` corollary with precise hypotheses.

## Phase 2 — arbitrary selection transport

Define only if necessary (or give helper predicates):

```text
A_S = activeSelectedIndices d S
A_T = activeSelectedIndices d T

M_in  = A_T \ A_S  -- new terms entering Body
M_out = A_S \ A_T  -- old terms leaving Body

sumMovedIn  = Σ k∈M_in  selectedTerm d k x u
sumMovedOut = Σ k∈M_out selectedTerm d k x u
```

Prove in **every CommSemiring**:

```text
selectedBody d T x u + sumMovedOut
  = selectedBody d S x u + sumMovedIn

selectedGap d T x u + sumMovedIn
  = selectedGap d S x u + sumMovedOut

selectedGap d S x u + selectedBody d S x u
  = selectedGap d T x u + selectedBody d T x u
```

The last balance equivalence is already an immediate corollary of Step 001 and may be an adapter, not a second independent reconstruction proof.

Prefer a common part + disjoint movement partition using `Finset` sums. General arbitrary-S/T results must remain valid when the two sets overlap, are equal, empty, full, or contain out-of-range members. Show the two moved sets are disjoint if useful. Do not incorrectly write `Body_T = Body_S + sumMovedIn` when old terms are also removed.

### Interval/GTail adapter (recommended)

Given `r,s ≤ d` and appropriate direction, express transport between `Finset.Ico r (d+1)` and `Finset.Ico s (d+1)`. It may be stated with the existing `GTail_split_at` and `selectedBody_Ico` without a duplicate GTail definition. Keep index orientation explicit: k denotes the **power of x**, and increasing r removes terms from the selected Body.

## Phase 3 — a real, hypothesis-guarded invariant

Do not stop with the trivial Big equality. Demonstrate the exact mathematical conditions for moving terms without changing modular observations.

For natural coordinates, modulus `m : ℕ`, and arbitrary S,T, prove a **conditional** modular transport theorem (either use `Nat.ModEq` or equality of residues):

If every term in `M_in ∪ M_out` is divisible by `m`, then:

```text
selectedBody d S x u ≡ selectedBody d T x u (mod m)
selectedGap  d S x u ≡ selectedGap  d T x u (mod m)
```

Prove it from the semiring movement identities and modular reasoning. Use genuine hypotheses about each moved term; do not assert unconditional preservation.

If the generic modular theorem would disproportionately expand scope, prove a correct single-term modular-preservation adapter first and report what remains. Do **not** claim the generic contract complete without evidence.

## Phase 4 — expose what is NOT invariant

Implement independent regression cases illustrating loss/change of coefficient content when an endpoint enters Body.

At degree 7:

```text
S = Finset.Ico 1 7    -- only interior terms
T = insert 0 S        -- introduce the u^7 endpoint

coeffGCD 7 S = 7
coeffGCD 7 T = 1

selectedBody 7 T x u = selectedBody 7 S x u + u^7
selectedGap  7 S x u = selectedGap  7 T x u + u^7
```

This contrasts **Big invariant** versus **coefficient gcd not invariant**. Be clear that it is not contradictory for the factor structure to change across a balance-preserving transport. It is the intended observation mechanic.

Regression also must cover:
- Single-term insert and erase for `d=3` over an arbitrary `CommSemiring`.
- Arbitrary selection S/T with both entering and departing indices (e.g. `d=5, S={1,3}, T={2,3}`).
- Equal selection, empty ↔ full, out-of-range indices, and `d=0`.
- Zero coordinates and modular-preservation examples with moved coefficients divisible by p and a contrasting nonpreservation example.
- The interval adapter if implemented.
- Audits with `#print axioms` on new public theorem endpoints.

## Phase 5 — verification and delivery

Create:

- `DkMath/Lib/Cosmic/GTailTransport.lean`
- `DkMathTest/CosmicFormula/GTailTransport.lean` (or closest established test path)
- `source-inventory-003.md`
- `report-003.md`
- update `ROADMAP.md` status honestly.

Focused commands:

```text
lake build DkMath.Lib.Cosmic.GTailTransport
lake build DkMathTest.CosmicFormula.GTailTransport
lake build DkMath.Lib.Cosmic.GTailFactor DkMathTest.CosmicFormula.GTailFactor
```

Use the existing Lake environment and avoid needless full clean/rebuild or large parallel runs. Record exact commands, outputs, exit status and all public `#print axioms` results. No `sorry`, `admit`, extra `axiom`, `unsafe`, or FLT-theorem import into Lib. Keep repository source style, imports and comments consistent.

For final report, distinguish:
- **proved invariant:** Big balance; conditional modular observation with hypotheses;
- **variable observation:** Body/Gap content, support and factor shape;
- **research conjecture:** any FLT7 descent/closure from transported conditions.

Report Outcome B if transport instruments work but no genuinely new FLT7 obstruction follows; Outcome C for a false hoped-for invariant or a documented failed precondition. The distinction matters more than claiming progress.

**Stop at Step 003.** Do not implement `GTailSeven`, Norm-square identities, `DkMath.FLT.Seven.GTailBridge`, façade promotion, or an unconditional FLT7 claim until this instruction has been reviewed.
