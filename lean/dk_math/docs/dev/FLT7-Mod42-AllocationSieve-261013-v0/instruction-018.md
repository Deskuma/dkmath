# Codex instruction-018 — same-packet source prime-valuation ledger (no invented additive endpoint)

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Prior review: `review-017.md` — Part A accepted; constructive bridge Outcome B
Implementer: GPT-6.1 Sol (light)

## Change of research direction

Gate 017 proved the **conditional** source-indexed prime-power
obstruction but found no theorem constructing a finite additive
Fermat chart from the bare packet. In this gate, **do not**
re-run that impossible-looking chart-existence obligation
under a new name, and do not search more unrelated moduli.

Instead extract a mathematically useful **unconditional
same-packet source arithmetic invariant** that may later
restrict the actual core's prime factorization.

The starting source theorem is
`RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root`.
For the actual norm packet K of one
`p : RamifiedSignedRootRoutingPacket`, it gives

```text
M = internalDepthFourSeventhCore p = Int.natAbs K.innerSndRoot
N > 0
M*N = V*C
Nat.Coprime M N
7 ∤ N

V = K.quadratic.canonical.verticalGapRoot
C = K.quadratic.compensationRoot
```

The values V,C,N are source objects and not a
chart complement `s=M/r`.

## Part A — intrinsic source-prime valuation conservation

Inspect the existing source-indexed prime-support
theorem, `Nat.factorization`, `padicValNat` and
Mathlib prime valuation of products *before*
creating a new result. Do not duplicate a lemma
that already gives the exact valuation balance.

Mathematical proposed consequence (not yet Lean checked):

For any prime ℓ dividing **actual** M,

```text
ℓ ∤ N
v_ℓ(M) = v_ℓ(V) + v_ℓ(C).
```

Why: `Coprime M N` gives ℓ∤N; the source
equality `M*N=V*C` and valuation additivity
give the equality. Both V,C should be positive
because M,N>0 and their product equals V*C.
Verify any positivity/zero conventions required
by the exact valuation API, not just paper algebra.

A possible Lean-facing statement (adapt types,
source aliases and namespace after inspection):

```lean
theorem internalDepthFour_source_prime_valuation_balance
    (p : RamifiedSignedRootRoutingPacket)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (hdiv : ℓ ∣ internalDepthFourSeventhCore p) :
    ∃ N : ℕ,
      0 < N ∧
      Nat.Coprime (internalDepthFourSeventhCore p) N ∧
      internalDepthFourSeventhCore p * N =
        p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
          .quadratic.canonical.verticalGapRoot *
        p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
          .quadratic.compensationRoot ∧
      ¬ ℓ ∣ N ∧
      padicValNat ℓ (internalDepthFourSeventhCore p) =
        padicValNat ℓ
          (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
            .quadratic.canonical.verticalGapRoot) +
        padicValNat ℓ
          (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
            .quadratic.compensationRoot)
```

The displayed API is **illustrative**; Lean elaboration
may require a `let K := ...`, different valuation
conventions or a dedicated small source certificate.
Prefer a clear usable theorem with the actual source
packet, not an unreadable giant declaration.

If the exact identity is already in Mathlib/DkMath,
reuse it and prove only a **new same-packet consequence**
that materially adds source information.

Optionally derive the weaker `ℓ|V ∨ ℓ|C`
from this fact, but identify it as likely overlapping
the existing
`internalDepthFourAllocation_prime_support`.
Do not describe the weaker rephrasing as major novelty.

## Part B — distinguish source provenance from chosen chart

Document what this valuation conservation does
and does not constrain. In particular:

1. It tracks prime support **inside the source norm
   product V*C**, on the *same p*, without hrec,
   hcore equality, or a newly supplied natural u,v.
2. It does **not** select `r` from the exact nested
   sieve nor produce `s=M/r`.
3. It does **not** give an upper bound
   `M/ℓ^n≤343` for every prime dividing M.
   Gate 016's conditional prime-power receiver exclusion
   cannot be applied to an arbitrary source M
   until the relevant factorization and coefficient
   bound are actually proved.
4. It does **not** prove `quotientRoot`, the
   real-pair gcd loads, or any stripped ring root
   equals the chart center or natural endpoint.
5. Bare p and `InternalDepthFourCounterexampleReconstructionObligation p`
   must remain separate. No additive chart
   existence is supplied by their equivalence.

Where possible, check explicit existing signatures
for source valuations/prime support. If one strong
source-only lemma identifies a real new constraint on
V or C (beyond their product) without a hidden
extra hypothesis, include it, but **only if proved**.
Do not assume `Coprime V C`, exclusive ownership,
or any bound that the live source does not supply.

## Part C — an honest feasibility conclusion

This is a small gate, not a framework-building project.
State clearly whether the new same-packet valuation
ledger gives a genuinely stronger restriction on M or
merely repackages M*N=V*C and coprimality. If it is
only a refactoring, say so and do **not** claim progress
toward FLT7 reconstruction existence.

Use `source-bridge-frontier-017.md` as baseline,
but do not repeat its table wholesale. Supply a
specific next **source-intrinsic** research hypothesis
only if its premises arise from actual p.

If the source invariants do not yield any nontrivial
core restriction, record the negative finding and
recommend a strategy reassessment rather than
another sequence of modular sieves.

## Scope, results and reports

**Outcome A:** a newly kernel-checked, unconditional
same-packet valuation-conservation theorem with
honest treatment of ℓ, zero/positivity and the
actual source product; plus a precise discussion
of its independence from additive-chart existence.

**Outcome B:** a valid weaker prime-support/source
lemma or duplicated existing invariant with an exact
mathematical explanation of the missing sharpening.

**Outcome C:** the proposed valuation formula is
false under the actual definitions, or a precise
Lean/API blocker was found and documented.

Run focused build/tests and `#print axioms` on
new exports. No `sorry`, `admit`, `sorryAx`,
fresh axioms, or unsafe proof substitutes.
Codex chooses local implementation and resource strategy.

Deliver `findings-018.md`, `report-018.md`,
compact `evidence/018-verification-summary.md` if
there are meaningful checks, and optionally a brief
`source-valuation-frontier-018.md` if needed.
Keep `logs/` transient.

**Codex only implements, verifies and reports.
Do NOT git add/stage/commit/push, create branches,
open PRs or merge. Stop after 018 for review.**
