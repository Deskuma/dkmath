# instruction-007 — Goldbach Pascal Overlap Hierarchy / Branch Closure

Date: 2026-09-10  
Branch: \`wip/NumberTheory-Goldbach-GNFiber-260910-v0\`  
Executor target: Luna Codex  
Status: final implementation checkpoint for this branch

## 0. Purpose

This is the **final checkpoint** of the current Goldbach branch.

Instruction-006 established:

$$
\operatorname{Incidence}
=
\operatorname{Covered}
+
\operatorname{OverlapExcess},
$$

$$
\operatorname{Survivors}
+
\operatorname{Incidence}
=
(n-1)+\operatorname{OverlapExcess},
$$

and an exact unordered prime-pair double count with

$$
\operatorname{OverlapExcess}
\le
\operatorname{PrimePairOverlapCount}.
$$

The next observation is that the local support multiplicities already form a Pascal hierarchy.

If

$$
k=
|\operatorname{goldbachObstructionSupport}(n,u)|,
$$

then

$$
\binom{k}{2}
=
(k-1)+\binom{k-1}{2}.
$$

Therefore the current pair-overlap inequality can be strengthened to an **exact decomposition**:

$$
\boxed{
\operatorname{PrimePairOverlapCount}
=
\operatorname{OverlapExcess}
+
\operatorname{PairOverlapResidual}.
}
$$

This branch should stop after making that exact Pascal structure explicit and, if inexpensive,
packaging the general local \`r\`-fold overlap multiplicity.

Do **not** begin product-wave / CRT sign-pattern localization, near/far splitting,
arbitrary-center mirror theorems, or any universal Goldbach escape argument here.

After this checkpoint is green and audited, prepare the branch for merge into \`develop\`.
The next development branch will be the GTail core promotion / refactor work described in:

\`\`\`text
lean/dk_math/docs/refact/Lib-GTail-Core-260908-v0/analysis-001.md
\`\`\`

The Goldbach work will resume after the canonical GTail/Pascal core surface is improved.

---

## 1. Read first

Current Goldbach additions:

\`\`\`text
DkMath/NumberTheory/Goldbach/Overlap.lean
DkMath/NumberTheory/Goldbach/PairOverlap.lean
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-006.md
\`\`\`

Relevant current declarations:

\`\`\`lean
goldbachObstructionSupport
goldbachLocalOverlapExcess
goldbachOverlapExcess
goldbachIncidenceConservation
goldbachPairAt_iff_incidence_lt_offsets_add_overlap

goldbachOffsetPrimePairMultiplicity
goldbachPrimePairs
goldbachPrimePairOverlapOffsets
goldbachPrimePairOverlapCount
goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity
goldbachOverlapExcess_le_primePairOverlapCount
\`\`\`

Also read the refactor note for terminology alignment:

\`\`\`text
docs/refact/Lib-GTail-Core-260908-v0/analysis-001.md
\`\`\`

Do not import GTail into Goldbach merely for this checkpoint unless a theorem is already generic
and introduces no architectural inversion.  The purpose here is to expose the Pascal structure,
not to prematurely couple the branch to unfinished refactor APIs.

---

## 2. Main implementation target — exact pair-overlap residual

Preferred owner:

\`\`\`text
DkMath/NumberTheory/Goldbach/PairOverlap.lean
\`\`\`

### 2.1 Local residual

Add:

\`\`\`lean
def goldbachLocalPairOverlapResidual (n u : ℕ) : ℕ :=
  Nat.choose ((goldbachObstructionSupport n u).card - 1) 2
\`\`\`

If a more natural but definitionally equivalent formulation simplifies proofs, document it.

Prove the local Pascal identity:

\`\`\`lean
theorem goldbach_pairMultiplicity_eq_localOverlap_add_residual
    (n u : ℕ) :
    goldbachOffsetPrimePairMultiplicity n u =
      goldbachLocalOverlapExcess n u +
        goldbachLocalPairOverlapResidual n u
\`\`\`

Mathematical content:

for \`k = support.card\`,

$$
\binom{k}{2}
=
(k-1)+\binom{k-1}{2}.
$$

Handle \`k=0,1\` carefully under natural subtraction.

Prefer a proof from standard \`Nat.choose\` identities / arithmetic.
Do not use an unproved combinatorial assertion.

### 2.2 Global residual

Add:

\`\`\`lean
def goldbachPairOverlapResidual (n : ℕ) : ℕ :=
  ∑ u ∈ goldbachOffsets n, goldbachLocalPairOverlapResidual n u
\`\`\`

Then prove:

\`\`\`lean
theorem goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual
    (n : ℕ) :
    goldbachPrimePairOverlapCount n =
      goldbachOverlapExcess n + goldbachPairOverlapResidual n
\`\`\`

This should use:

\`\`\`lean
goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity
\`\`\`

plus the local exact identity.

### 2.3 Existing inequality becomes a corollary

Refactor, if clean, the proof of

\`\`\`lean
goldbachOverlapExcess_le_primePairOverlapCount
\`\`\`

to follow immediately from the exact decomposition.

Do not break the public theorem name.

---

## 3. Optional but recommended — general local Pascal overlap multiplicity

If this can be implemented without destabilizing the branch, add a small generic local observer:

\`\`\`lean
def goldbachOffsetROverlapMultiplicity (n u r : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupport n u).card r
\`\`\`

Then prove only lightweight facts such as:

\`\`\`lean
@[simp] theorem goldbachOffsetROverlapMultiplicity_zero ...
@[simp] theorem goldbachOffsetROverlapMultiplicity_one ...
@[simp] theorem goldbachOffsetROverlapMultiplicity_two ...
\`\`\`

and, if Mathlib exposes a clean theorem, one Pascal recurrence:

\`\`\`lean
theorem goldbachOffsetROverlap_pascal ...
\`\`\`

Conceptually desired:

$$
\binom{k}{r}
=
\binom{k-1}{r-1}
+
\binom{k-1}{r}.
$$

However:

- do not spend excessive engineering effort on a generic recurrence;
- do not introduce a new abstraction hierarchy if Mathlib theorem alignment is awkward;
- do not build global triple/quadruple overlap ledgers yet.

The mandatory endpoint remains the exact pair decomposition in §2.

---

## 4. Structural documentation

Update module docstrings to state clearly:

1. obstruction multiplicity at one offset is organized by the Pascal row of
   \`support.card\`;
2. pair overlap is the \`r = 2\` layer;
3. overlap excess is the first repeated-obstruction payment;
4. the exact residual

$$
\operatorname{PairOverlapResidual}
=
\operatorname{PrimePairOverlapCount}
-
\operatorname{OverlapExcess}
$$

measures higher local multiplicity already present inside the pair ledger;
5. this suggests, but does not yet formalize, a connection to the future canonical
   GTail/Pascal tail filtration;
6. no Goldbach universal escape theorem is proved.

Do not claim an existing formal equivalence with \`GTail\` unless explicitly proved.

---

## 5. Regression targets

Add kernel-checkable regressions where practical.

At minimum:

### \`n = 2\`

Expected:

\`\`\`text
OverlapExcess = 0
PrimePairOverlapCount = 0
PairOverlapResidual = 0
\`\`\`

### \`n = 6\`

From report-006:

\`\`\`text
OverlapExcess = 1
PrimePairOverlapCount = 1
\`\`\`

Therefore expect:

\`\`\`text
PairOverlapResidual = 0
\`\`\`

Add a theorem proving the exact decomposition numerically or by the generic theorem.

### One center with support size at least 3

Search a small bounded range, preferably already inside the current test window,
for an offset where \`goldbachObstructionSupport n u\` has card at least \`3\`.

If found cheaply, add one regression demonstrating:

\`\`\`text
PrimePairOverlapCount > OverlapExcess
\`\`\`

or a positive local/global \`PairOverlapResidual\`.

If no small example appears quickly, record that fact in the report and do not enlarge the
search aggressively.

---

## 6. Branch closure report

Create:

\`\`\`text
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-007.md
\`\`\`

Include:

1. files changed;
2. exact local Pascal identity;
3. exact global pair-overlap decomposition;
4. regressions;
5. whether a positive residual example was found;
6. focused build results;
7. root build result;
8. axiom audit;
9. \`git diff --check\`;
10. explicit statement:
   **Strong Goldbach remains unproved**;
11. explicit branch conclusion:
   the fixed-center GN / obstruction / CRT / PCK / overlap / pair-overlap infrastructure
   is complete enough for this branch and should now be merged to \`develop\`;
12. next work:
   \`Lib-GTail-Core-260908-v0\` refactor before resuming Goldbach product-wave localization.

Update:

\`\`\`text
README.md
declaration-index.md
AxiomAudit.lean
DkMathTest/NumberTheory/GoldbachGNFiber.lean
\`\`\`

as appropriate.

---

## 7. Required verification

From \`lean/dk_math\`:

\`\`\`bash
./lean-build.sh DkMath.NumberTheory.Goldbach.PairOverlap
./lean-build.sh DkMath.NumberTheory.Goldbach
./lean-build.sh DkMathTest.NumberTheory.GoldbachGNFiber
lake env lean docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean
git diff --check
\`\`\`

Also run:

\`\`\`bash
./lean-build.sh DkMath
\`\`\`

Record existing unrelated root \`sorry\` warnings separately.

No new \`sorry\`, \`admit\`, or user axiom is allowed.

---

## 8. Stop boundary

After the exact Pascal pair-overlap decomposition and branch-closing report are green:

**STOP.**

Do not implement in this branch:

- product-modulus sign-pattern waves;
- LL / LR / RL / RR CRT decomposition;
- near/far product split;
- arbitrary-center mirror;
- PrimeWorld refinement specialized to Goldbach;
- short-fiber localization;
- universal capacity escape;
- any theorem claiming Strong Goldbach.

Those topics resume only after the GTail core refactor has established the canonical
Pascal / boundary / filtration APIs.

