# Codex Instruction — PRIM-L023 Full-Cover Old/Fresh Packet Branch Matrix Audit

Branch: `wip/number-theory-primitive-structure-260822-v2`

Project: DkMath NumberTheory Primitive Structure / Legendre first application

Environment: keep the repository on the current Lean / Mathlib v4.32.2 toolchain. Do not upgrade to v4.33.0 in this checkpoint.

## Checkpoint type

This is a **read-only mathematical/API reconnaissance**.

Do not modify Lean source files, imports, dependency revisions, `lean-toolchain`, Lake configuration, PRIM-C001/C002, PRIM-L022, or the Legendre facade/frontier.

The only requested repository change is the final report described below.

---

## Current verified state

PRIM-PAR-000 completed with:

```text
Outcome B — LOSSLESS COORDINATE
```

Valuation parity is available essentially for free from existing Mathlib/DkMath APIs, but no current theorem consumes that residue bit strongly enough to improve the Legendre full-cover frontier. Do not start PRIM-PAR-001 in this checkpoint.

The active exact arithmetic route is therefore the factor normal form produced by PRIM-C001/C002 and PRIM-L022.

For a positive square offset point

```text
m = n^2 + r,
1 ≤ r ≤ 2*n,
```

the generic square-Body theorem gives:

```text
old-generated
or
unique fresh prime ℓ > n × bounded old-generated cofactor k with 0 < k ≤ n.
```

For a **covered coprime seat**, PRIM-L022 sharpens the fresh branch to:

```text
unique fresh ℓ > n × nontrivial small cofactor k,
2 ≤ k ≤ n,
k ∈ squareAnchorCoprimeBaseOffsets n.
```

For a selected old support prime `p ≤ n`, PRIM-L022 also proves the dual quotient form

```text
squareOffsetSupportQuotient n p r = ℓ * (k / p)
```

and the exact compression

```text
quotient is prime
↔ k = p
↔ singleton old support + selected-prime depth one.
```

PRIM-L020 proves that the two complete points in one coprime packet are coprime. PRIM-L021 gives the corresponding reduced-residue / factor-rectangle geometry.

The purpose of PRIM-L023 is to lift the **single-seat old/fresh dichotomy** to the **two-seat packet level** and determine whether the resulting four branch types expose any genuinely new finite obstruction.

---

# Main packet geometry

Fix `n > 0` and a canonical coprime base offset `r`.

The packet points are

```text
L = n^2 + r
R = n^2 + (n + r) = L + n.
```

Under `SquareOffsetsFullyCovered n`, each side is individually one of:

```text
O = PrimeScaleGeneratedBy (primeScalesUpTo n) point

F = ∃ ℓ k,
      Prime ℓ,
      n < ℓ,
      2 ≤ k,
      k ≤ n,
      k ∈ squareAnchorCoprimeBaseOffsets n,
      ℓ * k = point,
      k old-generated,
      ℓ unique fresh for that point.
```

Therefore every fully-covered coprime packet lies in exactly one of the four conceptual branch cells:

```text
O / O
O / F
F / O
F / F
```

Do **not** assume that all four cells are inhabited, and do **not** assume any cell is impossible before checking the existing theorem graph.

The strongest immediately visible case is `F/F`:

```text
L = ℓ₁ * k₁
R = ℓ₂ * k₂
R - L = n
```

with

```text
ℓ₁, ℓ₂ > n prime
2 ≤ k₁, k₂ ≤ n
k₁, k₂ in the canonical coprime base world.
```

PRIM-L020 complete packet coprimality should imply cross-side separation such as

```text
Coprime k₁ k₂
Coprime ℓ₁ k₂
Coprime k₁ ℓ₂
Coprime ℓ₁ ℓ₂
```

when the hypotheses are available. Verify the exact existing theorem chain rather than reproving it.

The exact additive relation becomes

```text
ℓ₂ * k₂ - ℓ₁ * k₁ = n.
```

The reconnaissance question is whether this is only another exact coordinate rewrite, or whether the bounded cofactors `k₁,k₂ ≤ n` force a genuinely new injectivity, descent, cycle, cardinality, residue, or incompatibility statement.

---

# Required reconnaissance questions

Answer each question with exact declaration names and source paths when available.

## Q1 — packet-level branch predicates already present?

Search the current Legendre / Primitive source for any existing definitions or theorems that already package:

```text
old-generated left/right
fresh-split left/right
packet-level old/fresh alternatives
```

Classify:

```text
A. exact API already exists
B. equivalent theorem exists but is not packaged at packet level
C. genuinely missing
```

Do not add a new predicate merely because a four-cell table is aesthetically convenient.

## Q2 — can the four branch cells be made logically exact without new arithmetic?

Determine whether existing theorems are sufficient to prove, for every fully-covered coprime packet:

```text
(O/O) ∨ (O/F) ∨ (F/O) ∨ (F/F)
```

with pairwise disjointness if appropriate.

Important:

- `old-generated` and `fresh split` should be treated as the exact C002 alternatives.
- Do not confuse `FreshPrimeDirection` with `SupportDisjointFrom`.
- Do not assume fresh existence on an old-generated seat.

If exclusivity of O and F follows automatically from `PrimeScaleGeneratedBy` versus `FreshPrimeDirection`, identify the smallest existing theorem chain.

## Q3 — exact F/F factor rectangle

For an `F/F` packet, audit which of the following follow from existing PRIM-L020/L021/C002/L022 APIs without new proof ideas:

```text
L = ℓ₁ * k₁
R = ℓ₂ * k₂
R - L = n

2 ≤ k₁, k₂ ≤ n
k₁, k₂ ∈ squareAnchorCoprimeBaseOffsets n

Coprime L R
Coprime k₁ k₂
Coprime ℓ₁ k₂
Coprime k₁ ℓ₂
Coprime ℓ₁ ℓ₂
Coprime n k₁
Coprime n k₂
```

Also check the reduced-residue consequences modulo `n`.

Do not introduce `ZMod` if the existing `Nat.ModEq` API is sufficient.

## Q4 — does F/F force the fresh primes to be distinct?

This should look plausible from complete packet coprimality, but verify the exact Lean route.

Classify whether

```text
ℓ₁ ≠ ℓ₂
```

is already immediate and whether any stronger ordering relation follows from

```text
ℓ₂*k₂ - ℓ₁*k₁ = n,
ℓ₁,ℓ₂ > n,
k₁,k₂ ≤ n.
```

Do not infer `ℓ₁ < ℓ₂` merely from `R > L`; the cofactors differ.

## Q5 — small-cofactor return map

Investigate whether the fresh branch defines a useful finite map

```text
fresh coprime seat r  ↦  small cofactor k ≤ n
```

using existing uniqueness from C001/C002.

Questions:

1. Is `k` uniquely determined by the seat once a fresh prime exists?
2. Is the fresh prime `ℓ` uniquely determined? (Expected: yes, already C001.)
3. Does uniqueness of `ℓ` plus `ℓ*k = n^2+r` imply uniqueness of `k` trivially?
4. Can two distinct fresh seats have the same `k`?
5. If they can, what exact divisibility/additive relation follows?
6. Is injectivity available under any already-proved coprime-packet or quotient hypotheses?

Do not define the map unless an actual theorem consumer is identified.

## Q6 — packet F/F descent or self-return

The fresh cofactors return to the bounded canonical base world:

```text
k₁,k₂ ≤ n.
```

Audit whether existing APIs let one interpret `(k₁,k₂)` as a smaller instance of any already-defined packet/square-shell object.

Be strict here.

A numerical decrease alone is not a descent theorem. To count as a genuine descent candidate, identify:

```text
state type
reconstruction theorem
preserved hypotheses
strictly decreasing well-founded measure
```

If no such reconstruction exists, classify the return as a bounded coordinate return only.

Do not invent a recursive Legendre state in this checkpoint.

## Q7 — O/O and mixed branches

Audit the unresolved branches separately.

### O/O

Both packet points are generated entirely by primes `≤ n`, while the complete points are coprime.

Check whether existing support-disjointness, packet-support disjointness, totient/cardinality, or quotient theorems force any useful restriction on how the two old-generated factorizations can coexist.

### O/F and F/O

One side is entirely old-generated; the other has one fresh prime times a small old-generated cofactor.

Check whether complete packet coprimality forces the old support of the O-side to be disjoint not only from the fresh prime but also from the entire small cofactor on the F-side. If so, determine whether this yields any exact finite support partition or cardinality restriction.

Do not turn support disjointness into a density or probability claim.

## Q8 — interaction with L019/L020/L021 packet cross geometry

The older packet route selected old support primes `p,q` and obtained

```text
p*a + n = q*b
```

with cross-factor coprimality and unit-residue geometry.

Determine how this factor rectangle specializes or refactors when one or both complete packet points are in the C002 fresh branch.

In particular, for F/F compare:

```text
complete-point factorization:
  L = ℓ₁*k₁
  R = ℓ₂*k₂

selected-old factorization:
  L = p*a
  R = q*b
```

and PRIM-L022:

```text
a = ℓ₁ * (k₁/p)
b = ℓ₂ * (k₂/q).
```

Check whether substituting these into the packet equation gives any theorem stronger than the already-known exact identities.

If it only re-expresses the same equation, state that explicitly.

## Q9 — cardinality / matching leverage test

Without implementing Hall/matching machinery, determine whether the branch matrix exposes a finite set map with an obvious cardinality imbalance.

Potential objects to inspect only if already present:

```text
canonical coprime base offsets
fresh seats
small cofactors
old-generated seats
packet cross pairs
prime-world residues
```

Questions:

- Is the target set strictly smaller than the source set under full cover?
- Is any candidate map already injective/surjective by existing theorems?
- Does `k ∈ squareAnchorCoprimeBaseOffsets n` merely map a set of size `φ(n)` back into another set of size `φ(n)`, giving no contradiction?
- Is there any forced fixed-point-free permutation / involution / cycle structure?

Do not introduce matching machinery unless reconnaissance finds a concrete missing theorem that would immediately consume it.

## Q10 — final leverage classification

Classify the entire packet branch-matrix route as one of:

```text
Outcome A — DIRECT LEVERAGE
  Existing theorems already imply a new exclusion, strict cardinality bound,
  injectivity obstruction, descent mechanism, or contradiction against full cover.

Outcome B — STRUCTURAL REFINEMENT
  The O/F packet matrix is an exact and useful strengthening of the finite
  normal form, but no current theorem converts it into a stricter full-cover
  obstruction.

Outcome C — REDUNDANT REPACKAGING
  The four-cell matrix adds no mathematically useful information beyond
  existing L019–L022 theorem statements.
```

Do not force Outcome A.

---

# Expected report

Create only:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-packet-old-fresh-matrix-audit-260825.md
```

The report should contain:

1. Executive outcome A/B/C.
2. Exact current theorem inventory used.
3. Answers to Q1–Q10.
4. A branch table for O/O, O/F, F/O, F/F.
5. Exact F/F factor/coprimality/residue facts supported by current APIs.
6. Any candidate finite map, with explicit proof status for uniqueness/injectivity/surjectivity.
7. A descent feasibility verdict with the required state/reconstruction/measure checklist.
8. Explicit list of apparently attractive but invalid inferences.
9. Minimal recommendation for PRIM-L024, or an explicit recommendation to stop this route.
10. v4.32.2 / future-v4.33.0 API sensitivity notes only if actually encountered.

---

# Important invalid inferences to guard against

Do not silently use any of the following:

```text
fresh exists on every covered seat
fresh means support-disjoint
old-generated means prime
odd Ω means prime
F/F implies ℓ₁ < ℓ₂
k₁,k₂ ≤ n automatically defines a smaller Legendre packet
coprime complete points imply same-side factors are coprime
residue equality implies integer equality
finite return implies descent
same-cardinality finite map implies permutation without bijectivity
```

Preserve the exact distinction between:

```text
Direction
Depth
fresh finite-world support
support disjointness
PrimitiveBeam / Zsigmondy origin
```

---

# Non-goals

Do not add or modify Lean source.

Do not add:

- PRIM-PAR-001 parity wrappers;
- a new packet branch inductive type or enum;
- a new finite map definition unless the report proves it has an immediate consumer;
- Hall's theorem / matching infrastructure;
- third-order inclusion-exclusion;
- analytic prime estimates;
- PNT, Mertens, sieve asymptotics;
- `ZMod` infrastructure solely for this audit;
- Zsigmondy / PrimitiveBeam origin claims;
- RH/CFBRC dependencies;
- finite-difference or differential generalization;
- a recursive Legendre descent state;
- a proof of Legendre's conjecture.

This checkpoint is successful even if it proves that the packet old/fresh matrix is only a structural refinement and the route should stop.

---

# Verification

Since this checkpoint changes documentation only:

```sh
git diff --check
```

and perform the usual whitespace / forbidden-placeholder audit on the new report.

No Lean build is required unless local source inspection causes an incidental test file to be created; avoid creating such files.

Report the final outcome and any concrete next theorem candidate. Do not begin PRIM-L024 automatically.