# Codex Instruction — PRIM-QR-000 Square-Anchor Quadratic-Residue Constraint Audit

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: keep the current Lean / Mathlib v4.32.2 toolchain. Do not upgrade.

## 0. Checkpoint classification

This is a **read-only mathematical/API reconnaissance**.

Do not modify Lean source files, theorem statements, docstrings, imports, dependency revisions, `lean-toolchain`, Lake configuration, PRIM-C001/C002, PRIM-L022, the Legendre facade/frontier, or the previous audit reports.

Create exactly one report:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-square-anchor-quadratic-residue-audit-260825.md
```

Do not start a follow-up implementation checkpoint automatically.

---

# 1. Motivation

PRIM-JAC-000 identified the exact hard frontier as the **square-anchored** coprime escape

```text
∀ n > 0, ∃ r, 1 ≤ r ∧ r ≤ 2*n ∧
  Nat.Coprime (n^2+r) (primeWorldModulus (primeScalesUpTo n)).
```

and established that the uniform Jacobsthal bound is a strictly stronger target and fails at the required scale.

The next audit must therefore use information that disappears when the starting point `n^2` is replaced by an arbitrary interval anchor.

The candidate square-specific fact is:

```text
q ∣ n^2 + r
```

which gives, modulo `q`,

```text
n^2 ≡ -r.
```

For an odd prime `q` with `q ∤ n`, this says that `-r` is a nonzero quadratic residue modulo `q`.

The question is not whether this observation is true. The question is whether it gives a **new aggregate restriction on full cover** beyond the exact one-residue-class wave condition already formalized in `Legendre.Wave` / `Basic`.

---

# 2. Existing DkMath surface to inspect first

Inspect the current branch, especially:

```text
DkMath.NumberTheory.Legendre.Basic
DkMath.NumberTheory.Legendre.Wave
DkMath.NumberTheory.Legendre.CoprimePacket
DkMath.NumberTheory.Legendre.PairOverlap
DkMath.NumberTheory.Legendre.PacketCross
DkMath.NumberTheory.Legendre.PacketCoprimality
DkMath.NumberTheory.Legendre.PacketUnitResidue
DkMath.NumberTheory.Legendre.SmallCofactor
DkMath.NumberTheory.Legendre.Frontier
DkMath.NumberTheory.Primitive.FinitePrimeWorld
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
```

Locate the exact declarations for:

```text
SquareOffsetForbiddenBy
squareAnchorForbiddenResidue
squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
squareOffsetAnchorNondivisorSupport
squareOffsetPrimeSupport
SquareOffsetCovered
squareAnchorCoprimeOffsets / squareAnchorCoprimeBaseOffsets
packet left/right modular identities
```

Do not duplicate any congruence already available.

Also inspect the **actual Mathlib v4.32.2 checkout** under `.lake/packages/mathlib` for existing APIs for:

```text
quadratic residues / IsSquare in ZMod q
Legendre symbol / Jacobi symbol if present
quadratic reciprocity
(-1 / q) or the q mod 4 classification of -1
```

Do not assume theorem names from newer Mathlib versions. Record exact v4.32.2 names and import paths if useful.

If a Legendre-symbol API is awkward or absent, the minimal semantic statement is simply a square witness in `ZMod q`; do not introduce a new symbol abstraction for this audit.

---

# 3. Q1 — exact local square witness

For a coprime square offset `r` and an old nondivisor support prime `q`, verify the smallest existing theorem chain giving:

```text
Nat.Prime q
q ≤ n
¬ q ∣ n
q ∣ n^2+r
```

and hence, for odd `q`,

```text
-r is a nonzero square modulo q,
```

with witness `n mod q`.

Also verify that the same assumptions force

```text
¬ q ∣ r.
```

Classify this as one of:

```text
A. directly exposed by existing DkMath/Mathlib theorems
B. a thin rewrite/composition only
C. requires genuinely new infrastructure
```

No Lean theorem should be added in this checkpoint.

Treat `q = 2` separately. Do not silently apply odd-prime symbol facts to `2`.

---

# 4. Q2 — character form of the forbidden residue

For odd prime `q` with `q ∤ n` and `q ∣ n^2+r`, investigate the exact consequence

```text
(r / q) = (-1 / q)
```

in whatever v4.32.2 Mathlib notation exists, or equivalently the residue classification:

```text
q ≡ 1 (mod 4)  → r is a nonzero quadratic residue mod q
q ≡ 3 (mod 4)  → r is a quadratic nonresidue mod q
```

because `r ≡ -n^2 (mod q)`.

Check the precise assumptions needed for this statement, especially `q ∤ r` and oddness.

Do not call this new information if it is merely a weaker corollary of the already exact condition

```text
r ≡ squareAnchorForbiddenResidue n q (mod q).
```

The report must explicitly compare the information content:

```text
exact forbidden residue class
vs.
quadratic-character class
```

and say which direction of implication holds.

---

# 5. Q3 — full-cover quadratic witness condition

On the canonical coprime offsets, formulate report-local notation for the necessary full-cover statement:

```text
for every r in squareAnchorCoprimeOffsets n,
there exists an old nondivisor prime q ≤ n such that
q ∣ n^2+r,
```

and therefore, for odd witness `q`,

```text
-r is a nonzero square mod q.
```

Audit whether this condition actually removes any candidate witness primes that the existing exact support API did not already remove.

The key question is:

> Does the quadratic-character projection permit a useful aggregate count or incompatibility across many offsets, or does it only forget information from the exact wave congruence?

Do not infer leverage merely because the statement sounds more number-theoretic.

---

# 6. Q4 — special offsets

Inspect whether particular canonical offsets produce genuinely sharper witness restrictions.

At minimum examine:

```text
r = 1
r = n-1 when admissible
r = n+1 when admissible / packet companion interpretation
small prime r
odd prime r in the canonical base range
```

For example, `q ∣ n^2+1` with odd prime `q` forces `-1` to be a square modulo `q`, hence `q ≡ 1 (mod 4)`.

Determine whether any such local restriction can be turned into a **full-cover obstruction**, rather than a fact about one chosen seat.

Do not claim that `n^2+1` must be prime; it need not be.

---

# 7. Q5 — quadratic reciprocity as a possible direction reversal

For offsets `r` that are themselves odd primes (or under another clean hypothesis), inspect whether quadratic reciprocity can turn

```text
(-r / q) = 1
```

into a restriction on `q mod r` or on the set of admissible witness primes `q ≤ n`.

Record the exact formula and all congruence cases if this is useful.

Then answer the important question:

> Does reciprocity give a restriction that couples different witness primes / different offsets, or is it still only a per-seat restatement?

Do not introduce Dirichlet, PNT in progressions, Burgess bounds, GRH, or analytic distribution theorems unless they are only mentioned as **external missing providers**. They must not become dependencies or hidden assumptions.

---

# 8. Q6 — interaction with packet geometry

For a coprime packet `(r, n+r)`, if the left and right seats are covered by primes `p` and `q`, compare the two conditions

```text
p ∣ n^2+r
q ∣ n^2+n+r.
```

Audit whether quadratic-character information adds anything beyond the already implemented:

```text
p*a + n = q*b
cross-side coprimality
product congruence modulo n
one-anchor determinant
```

Check especially whether the pair of square-residue conditions can force:

```text
p ≠ q               -- already known by packet coprimality
p/q mod 4 pattern
an impossible simultaneous character pattern
new pair-count deficit
```

If none follows, say so explicitly.

---

# 9. Q7 — interaction with old/fresh and small-cofactor geometry

Audit whether the quadratic-character constraint distinguishes:

```text
old-generated seat
unique-fresh × small-cofactor seat
```

or whether it depends only on the selected old covering prime and therefore ignores the C002/L022 branch split.

A useful result would need to constrain one of the unresolved branches, not merely decorate its witness prime.

Do not infer `FreshPrimeDirection` from a quadratic residue condition.

---

# 10. Q8 — counting leverage

Test the strongest finite combinatorial consequence available **without adding analytic distribution hypotheses**.

Possible report-local questions:

1. For fixed odd `q`, how many residue classes satisfy the quadratic-character condition compared with the single exact forbidden wave class?
2. Does replacing exact waves by character-compatible classes make the cover problem stronger or weaker?
3. Can a union bound, character sum identity, or exact finite count on the interval `1..2n` prove that not all canonical coprime offsets are coverable?
4. Does any such count beat the existing exact wave / pair-overlap / localized obstruction ledger?

Be alert to the likely direction:

```text
exact wave condition ⇒ character condition
```

so character projection may enlarge each witness set and therefore weaken the obstruction.

If this is what happens, record it as a decisive negative result.

---

# 11. Q9 — relation to the exact hard frontier

The report must state whether the square-character condition yields any theorem of the schematic form

```text
SquareOffsetsFullyCovered n
  → NEW_CONSTRAINT(n)
```

where `NEW_CONSTRAINT(n)` is **strictly stronger** than the currently known exact support/wave statements and has a plausible route to contradiction.

Distinguish:

```text
new exact coordinate
weaker projection of an existing coordinate
new aggregate inequality
new contradiction/provider
```

Do not classify a weaker projection as progress merely because it uses quadratic reciprocity terminology.

---

# 12. Required final classification

Choose exactly one:

```text
Outcome A — DIRECT QUADRATIC LEVERAGE
```

Use only if the audit finds a genuinely stronger aggregate constraint on full cover, a branch exclusion, a strict counting deficit, or another concrete route not already present in the exact wave API.

```text
Outcome B — SQUARE-SPECIFIC STRUCTURAL REFINEMENT
```

Use if the quadratic interpretation is mathematically meaningful and square-anchor specific, but no stronger full-cover obstruction follows.

```text
Outcome C — WEAKER PROJECTION / REDUNDANT
```

Use if quadratic-character data is strictly weaker than the exact forbidden-residue wave information and supplies no independent useful coordinate.

If the outcome is B or C, recommend stopping this route and do not propose an implementation layer automatically.

---

# 13. Required report contents

The report must include:

1. executive outcome;
2. exact DkMath theorem inventory;
3. exact Mathlib v4.32.2 quadratic-residue / reciprocity API inventory;
4. q=2 versus odd-prime separation;
5. proof chain for `q ∣ n^2+r → -r is square mod q`;
6. character / mod-4 classification where valid;
7. information comparison against `squareAnchorForbiddenResidue`;
8. full-cover necessary condition in quadratic language;
9. special-offset audit;
10. reciprocity audit;
11. packet interaction;
12. old/fresh interaction;
13. finite counting leverage test;
14. exact hard-frontier implication test;
15. final A/B/C classification and stop/go recommendation.

Keep repository-derived facts, Mathlib API facts, and any external mathematical references clearly separated.

---

# 14. Non-goals / forbidden escalation

Do not:

- modify Lean source or docstrings;
- add `ZMod` infrastructure merely for this report;
- add a Legendre/Jacobi symbol wrapper;
- add quadratic reciprocity dependencies to Primitive/Legendre;
- add analytic prime-distribution assumptions;
- invoke GRH/RH/CFBRC;
- claim that a quadratic-residue necessary condition is sufficient for coverage;
- replace the exact wave condition by a weaker character condition in existing theorems;
- claim a full-cover contradiction unless an explicit theorem chain supports it;
- start PRIM-QR-001 automatically.

The purpose of PRIM-QR-000 is to test whether the **square** in the square anchor gives arithmetic leverage that the Jacobsthal reformulation necessarily forgets.
