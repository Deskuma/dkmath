# Codex Instruction — PRIM-ST-000 Square-Shell Exact Wave Transport / Prime-World Growth Audit

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

## 0. Mission

This is a **read-only mathematical/API reconnaissance checkpoint**.

Do not modify Lean source, theorem statements, docstrings, imports, facades, toolchain files, Lake configuration, PRIM-C001/C002, PRIM-L022, or existing Legendre modules.

The previous audits established:

- PRIM-PAR-000: parity is a lossless coordinate but no current full-cover lever.
- PRIM-L023: old/fresh packet matrix is structural refinement only.
- PRIM-FD-000: finite-difference identities are algebraic/geometric refinement only.
- PRIM-JAC-000: the exact hard frontier is the square-anchored coprime escape, not the global Jacobsthal bound.
- PRIM-QR-000: quadratic-character constraints are a weaker projection of the exact forbidden residue wave.

Therefore this checkpoint must **retain the exact residue information** and change the direction of observation: instead of refining one fixed shell, study how the exact square-anchor waves evolve under

```text
n -> n + 1.
```

The central question is:

> Does the simultaneous evolution of the square anchor and the finite prime world produce a genuine shell-to-shell obstruction, descent, or incompatibility for full cover?

The intended output is a report only:

```text
primitive-square-shell-wave-transport-audit-260825.md
```

Do not start a follow-up implementation checkpoint automatically.

---

## 1. Required source inventory

At minimum inspect the current declarations in:

```text
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/Wave.lean
DkMath/NumberTheory/Legendre/CoprimePacket.lean
DkMath/NumberTheory/Legendre/PacketCross.lean
DkMath/NumberTheory/Legendre/PacketCoprimality.lean
DkMath/NumberTheory/Legendre/Frontier.lean
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean
```

Also search the current repository for existing declarations involving:

```text
squareAnchorForbiddenResidue
SquareOffsetForbiddenBy
primeScalesUpTo
primeWorldModulus
supportDisjointFrom_insert_prime_iff
primeWorldChild
reservedChildIndices
survivingChildIndices
n + 1
succ
shell transport
anchor transport
```

Do not assume a bridge is missing until the current source is checked.

---

## 2. Q1 — exact forbidden-phase recurrence in the anchor variable

Let report-local notation be

```text
A_q(n) := squareAnchorForbiddenResidue n q.
```

Since

```text
(n+1)^2 = n^2 + (2*n+1),
```

the expected exact modular transport is

```text
A_q(n+1) + (2*n+1) ≡ A_q(n) [MOD q].
```

Audit the smallest existing theorem chain proving this.

Prefer `Nat.ModEq` / exact modulo statements. Do not introduce quadratic characters, real finite differences, or `ZMod` unless genuinely required.

Also determine whether the canonical representatives imply a convenient `% q` equality, and whether

```text
A_q(n+q) = A_q(n)
```

is already derivable as an exact equality of canonical residues.

Classify each result as:

```text
A. existing public theorem
B. thin rewrite/composition
C. genuinely missing semantic bridge
```

Do not implement it in this checkpoint.

---

## 3. Q2 — exact point transport between consecutive square anchors

Audit the exact identity

```text
(n+1)^2 + r = n^2 + (2*n+1+r).
```

For a fixed old prime `q <= n`, determine the precise equivalence between

```text
q | (n+1)^2 + r
```

and the corresponding old-anchor divisibility statement at the shifted offset

```text
2*n+1+r.
```

Important: this shifted coordinate lies **outside** the old Legendre shell `1 .. 2*n`.

Do not silently relabel it as a previous-shell offset.

The report must state explicitly whether this is:

- a useful transport into an extended offset window,
- only a tautological point identity,
- or enough to connect two actual `squareOffsets` Finsets.

---

## 4. Q3 — finite prime-world evolution from `n` to `n+1`

Audit the exact set evolution of

```text
primeScalesUpTo n
```

under `n -> n+1`.

Separate the two cases.

### Composite/non-prime insertion step

If `n+1` is not prime, determine whether current API gives

```text
primeScalesUpTo (n+1) = primeScalesUpTo n.
```

### Prime insertion step

If `q := n+1` is prime, determine whether current API gives

```text
primeScalesUpTo q = insert q (primeScalesUpTo n).
```

and then connect this, without reproving CRT machinery, to:

```text
supportDisjointFrom_insert_prime_iff
primeWorldModulus_insert
existsUnique_child_dvd_new_prime
reservedChildIndices_eq_singleton
card_survivingChildIndices
```

The key question is not merely that the prime world refines, but whether the **actual square-shell positions** at the new anchor align with the canonical refinement children in a useful way.

Do not assume such alignment.

---

## 5. Q4 — new-prime wave on a prime anchor

Let `q := n+1` and assume `Nat.Prime q`.

The new shell is anchored at `q^2`, so the new prime direction satisfies

```text
q | q^2 + r  <->  q | r.
```

Within the new square shell

```text
1 <= r <= 2*q,
```

audit whether the new `q`-wave occupies exactly

```text
r = q
r = 2*q.
```

If yes, classify carefully what this means:

- exactly two incidences of the **new q-wave**,
- not necessarily two newly covered seats, because old waves may overlap them.

Then determine the exact consequence of full cover for the remaining coprime seats. In particular, for prime anchor `q`, audit the statement that all offsets coprime to `q` must be covered by primes `< q`.

Check how much of this is already present in `CoprimePacket` and related theorems.

---

## 6. Q5 — compare shell `q-1` with the coprime part of prime shell `q`

For prime `q`, note the cardinality coincidence

```text
card (squareOffsets (q-1)) = 2*(q-1)
```

and

```text
card (squareAnchorCoprimeOffsets q) = 2*totient q = 2*(q-1).
```

Audit whether there is any **natural support-preserving map** between these two finite sets.

Possible report-local candidate maps may skip the two multiples `q` and `2*q`, but do not introduce a Lean definition.

For every candidate, test whether old-prime divisibility is actually preserved.

A bare cardinality equality is not a matching theorem.

Classify:

```text
A. exact support-preserving bijection exists
B. only a set/cardinality correspondence exists
C. no useful transport exists
```

---

## 7. Q6 — anchor-phase orbit of a fixed prime

For fixed prime `p`, the phase

```text
A_p(n) = -n^2 mod p
```

is periodic in `n mod p`.

Audit the exact finite orbit over one anchor period `0 <= n < p`:

- number of distinct phases,
- multiplicity of zero,
- multiplicity of nonzero phases,
- relation to the already-audited quadratic-residue projection.

The purpose is **not** to reintroduce Legendre symbols. The purpose is to see whether anchor-time phase multiplicity yields a new exact statement about consecutive shells that was invisible in the static PRIM-QR-000 audit.

If it only restates that square residues occur twice, mark it redundant.

---

## 8. Q7 — consecutive-full-cover transport test

Assume, only for the audit,

```text
SquareOffsetsFullyCovered n
SquareOffsetsFullyCovered (n+1).
```

Determine whether the exact phase recurrence and world evolution force any new joint constraint not already present in the two independent full-cover hypotheses.

Test at least:

1. composite step (`n+1` not prime): same prime world, shifted anchor;
2. prime step (`n+1` prime): one-direction world refinement;
3. whether an old support witness can be transported from one shell to the next;
4. whether a fresh hole in one shell forces a hole in the adjacent shell;
5. whether pair/packet coprimality survives the shell shift;
6. whether any strict count deficit appears over the union of two consecutive shells.

Do not infer persistence merely from periodicity or equal cardinality.

---

## 9. Q8 — minimal-counterexample / descent test

Suppose report-locally that `n` is a least positive anchor with full cover.

Audit whether the shell-transport identities provide any valid implication of the form

```text
full cover at n
  -> full cover at some m < n
```

or any reconstruction of a smaller Legendre state.

The following are **not** enough:

```text
same prime world
bounded shifted offset
small cofactor <= n
periodic phase
cardinality equality
```

A descent requires:

- a well-defined smaller state,
- preserved cover hypotheses,
- a strict measure decrease,
- a reconstruction theorem.

If any one is absent, classify the descent attempt as invalid.

---

## 10. Q9 — interaction with existing PrimeWorldRefinement

The generic refinement theorem uses canonical children

```text
r + j * primeWorldModulus S,
0 <= j < q.
```

The actual square-shell movement uses the additive displacement

```text
2*n+1.
```

Audit whether these coordinate systems ever align in the Legendre application at the relevant scale.

Do not assume `2*n+1` is a multiple of the old modulus; for large `n` it is normally tiny compared with the primorial modulus.

The report must say explicitly whether `PrimeWorldRefinement` provides:

- direct shell transport,
- only abstract finite-world refinement,
- or a useful bridge at prime insertion steps only.

---

## 11. Final leverage classification

Choose exactly one.

### Outcome A — DIRECT SHELL-TRANSPORT LEVERAGE

Use only if the audit finds a genuine new consequence such as:

- full cover at one shell forces an impossible adjacent-shell condition;
- prime insertion produces a strict deficit;
- a smaller fully covered shell is reconstructed;
- or a new exact two-shell inequality is obtained that is stronger than existing independent shell ledgers.

### Outcome B — EXACT DYNAMIC STRUCTURAL REFINEMENT

Use if the audit finds exact shell-to-shell phase/world transport that is mathematically new/useful as coordinates, but no contradiction, descent, or stronger full-cover obstruction.

### Outcome C — TAUTOLOGICAL TRANSLATION / NO NEW LEVERAGE

Use if all shell transport reduces to

```text
(n+1)^2 = n^2 + 2*n+1
```

plus already-known prime-world insertion/periodicity, without a useful application-level coupling.

Do not choose A because the formulas are aesthetically strong.

---

## 12. Report requirements

Create only:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-square-shell-wave-transport-audit-260825.md
```

The report must contain:

1. executive outcome;
2. exact repository theorem inventory;
3. Q1-Q9 answers;
4. a table separating anchor movement from prime-world movement;
5. explicit prime-insertion case analysis;
6. exact statements versus report-local notation;
7. rejected false transports/descent arguments;
8. final recommendation: implement / keep as coordinate / stop route.

No Lean build is required because no Lean source may be modified.

Run only repository hygiene checks appropriate to the report change, including `git diff --check`, whitespace inspection, and placeholder/forbidden-word audit used by the current project workflow.

---

## 13. Hard non-goals

Do not:

- prove or claim Legendre's conjecture;
- add a new shell-transport Lean module;
- add a new `Finset` or state machine merely for convenience;
- add Legendre-symbol or quadratic-reciprocity imports;
- restart the Jacobsthal route;
- restart parity infrastructure;
- introduce analytic sieve/PNT/RH/CFBRC dependencies;
- infer a support-preserving bijection from equal cardinalities;
- infer descent from `k <= n` or from a shifted coordinate;
- change Lean / Mathlib from v4.32.2.

Stop after the report.