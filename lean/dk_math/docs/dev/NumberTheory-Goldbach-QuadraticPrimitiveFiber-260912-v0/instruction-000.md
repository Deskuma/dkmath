# instruction-000 — Astra fact-discovery audit for the quadratic primitive Goldbach fiber

Date: 2026-09-12  
Branch: `research/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0`  
Executor target: GPT-6 Astra Codex  
Mode: **research / fact-discovery only**

## 0. Mission

Use Astra's reasoning budget to determine whether the newly available canonical GTail boundary theorems create a genuinely stronger Goldbach route at degree two, or merely re-express the already implemented fixed-center CRT/capacity ledger.

This is **not** an implementation sprint and **not** a request to prove Strong Goldbach.

The task is to:

1. formalize candidate facts in scratch Lean;
2. numerically stress-test them in Python;
3. search the repository for existing equivalent or stronger theorems;
4. distinguish exact new information from coordinate changes / equivalent reformulations;
5. leave incremental written reports throughout the investigation rather than only a final answer.

If a candidate is false, produce the smallest clear counterexample and record it. If a candidate is true but equivalent to an existing Goldbach capacity condition, classify it as **no information gain** rather than presenting it as progress toward Strong Goldbach.

---

## 1. Current formal baseline on `develop`

Read the current repository first. In particular:

```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GTailPascal.lean
DkMath/Lib/Cosmic/GTailBoundary.lean
DkMath/Lib/Cosmic/GTailCongruence.lean
DkMath/Lib/Cosmic/GTailPadic.lean
DkMath/Lib/Cosmic/GTailCyclotomic.lean

DkMath/NumberTheory/Goldbach/Basic.lean
DkMath/NumberTheory/Goldbach/Obstruction.lean
DkMath/NumberTheory/Goldbach/PrimeWorld.lean
DkMath/NumberTheory/Goldbach/Cardinality.lean
DkMath/NumberTheory/Goldbach/Capacity.lean
DkMath/NumberTheory/Goldbach/Conservation.lean
DkMath/NumberTheory/Goldbach/Overlap.lean
DkMath/NumberTheory/Goldbach/PairOverlap.lean
DkMath/NumberTheory/Goldbach/Limitations.lean
```

Also read:

```text
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/README.md
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-004.md
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-006.md
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-007.md

docs/refact/Lib-GTail-Core-260908-v0/analysis-001.md
docs/refact/Lib-GTail-Core-260908-v0/analysis-002.md
docs/refact/Lib-GTail-Core-260908-v0/gtcore-002.md
docs/refact/Lib-GTail-Core-260908-v0/gtcore-003.md
docs/refact/Lib-GTail-Core-260908-v0/gtcore-004.md
docs/refact/Lib-GTail-Core-260908-v0/gtcore-005.md
```

If the current workspace contains the latest `__dkmath-all.lean.txt.gz`, use `zgrep`/`zcat` as a repository-wide theorem database in addition to `rg`. Do not rely on one search vocabulary. Search also by mathematical shape: `gcd`, `Coprime`, `mirror`, `support`, `left`, `right`, `pair`, `CRT`, `primeWorld`, `primitive`, `parity`, `odd`, `even`, `Nat.choose`, `GTail`, `GN 2`, and related theorem statements.

### Already proved facts that must not be rediscovered as conjectures

The Goldbach branch already formalizes the fixed-center coordinates

```text
x = n - u
GN 2 x u = n + u
```

and exact equivalence with the usual Goldbach pair statement at center `n`.

It also formalizes the complete finite obstruction search, full-period CRT counting, exact survivor criterion, capacity equivalence, overlap ledger, and Pascal pair residual. Strong Goldbach remains unproved.

The GTail refactor now provides, among other things:

```lean
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
gcd_GN_eq_gcd_of_one_le
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
prime_dvd_GN_iff_dvd_gap
GTail_split_at
```

The degree-two specialization of the canonical gcd boundary is a principal object of this investigation.

---

## 2. Core research question

Determine whether the following normalization gives **strictly stronger finite structure** than the existing Goldbach obstruction/capacity ledger:

```text
fixed center n
  ↓
positive offset u
  ↓
primitive normalization: gcd(n,u)=1
  ↓
opposite parity / odd reflected endpoints
  ↓
left endpoint n-u and right endpoint n+u are coprime
  ↓
left/right obstruction supports separate
  ↓
pair overlap splits into LL / LR / RR
  ↓
LR becomes a product-modulus CRT wave
  ↓
possible new short-fiber localization or capacity gain
```

The key audit question is:

> Does primitive + parity normalization produce a real information gain, or does the reduced obstruction set exactly compensate for the reduced candidate set so that the result is equivalent to the existing CRT/capacity formulation?

Do not answer this by intuition. Prove or refute the relevant intermediate statements in Lean and compare exact finite counts numerically.

---

## 3. Phase QP-000 — environment and theorem inventory

Before proving new facts:

1. record the branch HEAD and relevant imported modules;
2. search for existing theorems that already imply any of the proposed primitive/parity statements;
3. record exact declaration names and owners;
4. identify whether Mathlib already has the required gcd/parity lemmas;
5. record any theorem that makes a proposed scratch theorem redundant.

Create immediately:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-000.md
```

This report must be committed **before** moving to the next phase. Do not postpone all reporting until the end.

---

## 4. Phase QP-001 — primitive reduction and quadratic boundary

Use scratch Lean to test and prove the strongest correct versions of the following candidate facts.

### 4.1 Coordinate coprimality

Investigate equivalences such as, under the required natural subtraction bound,

```text
Coprime n u ↔ Coprime (n-u) u
```

and the analogous right-endpoint statements if useful.

Prefer existing Mathlib/DkMath theorems where available.

### 4.2 Degree-two boundary gcd

Derive the Goldbach specialization of the canonical Lib theorem rather than reproving the mathematics ad hoc when possible.

Target mathematical form:

$$
\gcd(n-u,n+u)=\gcd(n-u,2)
$$

under the correct primitive hypotheses.

Then determine the exact strongest parity corollary:

$$
\gcd(n,u)=1,\quad n\not\equiv u\pmod 2
\Longrightarrow
\gcd(n-u,n+u)=1.
$$

Check edge cases `u = 0`, `n = 0,1,2`, and natural subtraction explicitly.

### 4.3 Prime pair implies primitive

Investigate and kernel-check the strongest correct form of:

```text
u > 0
Prime (n-u)
Prime (n+u)
→ Coprime n u
```

Do not assume this statement without proof. If an extra admissibility hypothesis is required, include it.

Also isolate the diagonal case `u = 0` and determine the exact theorem separating:

```text
center prime → diagonal Goldbach pair
```

from the positive-offset primitive search.

### 4.4 Primitive Goldbach search space

Define **scratch-only** candidate sets for:

```text
primitive offsets
primitive positive offsets
primitive parity-compatible offsets
```

and prove exact membership theorems.

Do not add these definitions to production `DkMath` modules in this research branch.

Create and commit:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-001.md
```

Report which statements are proved, false, redundant, or require stronger hypotheses.

---

## 5. Phase QP-002 — obstruction simplification on the primitive fiber

Investigate exact changes to the finite obstruction world after primitive/parity restriction.

### 5.1 Center-prime factors

Test/prove the candidate:

```text
Prime r
r ∣ n
Coprime n u
→ ¬ r ∣ n-u ∧ ¬ r ∣ n+u
```

with the correct natural-number assumptions.

If true, determine whether every prime divisor of the center may be removed from the obstruction world on the primitive fiber.

### 5.2 Parity prime

Determine exactly when prime `2` can be removed after parity normalization.

Do not conflate:

```text
raw divisibility obstruction
```

with

```text
proper obstruction
```

because endpoint-equals-prime exceptions are already known to break naive periodicity.

### 5.3 Left/right support separation

Create scratch left/right proper obstruction supports and test the candidate disjointness theorem.

Desired shape:

```text
primitive + parity-compatible seat
→ leftSupport ∩ rightSupport = ∅
```

Find the weakest correct assumptions.

If false, produce the smallest counterexample and explain whether the failure is caused by parity, endpoint exceptions, or a genuine shared odd factor.

Create and commit:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-002.md
```

---

## 6. Phase QP-003 — exact overlap decomposition

If QP-002 gives disjoint left/right supports, test an exact local decomposition.

For support cardinalities `L = |leftSupport|`, `R = |rightSupport|`, investigate:

$$
\binom{L+R}{2}
=
\binom{L}{2}+LR+\binom{R}{2}.
$$

Lift this to the existing Goldbach pair-overlap ledger if possible **in scratch only**.

Classify the three pieces:

```text
LL : two left obstruction primes
LR : one left and one right obstruction prime
RR : two right obstruction primes
```

The purpose is not the combinatorial identity itself; the purpose is to determine whether the `LR` term has an arithmetic property not present in the unsplit pair ledger.

Create and commit:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-003.md
```

---

## 7. Phase QP-004 — LR product-modulus / CRT audit

For distinct odd primes `p,q` in left/right roles, test the exact raw congruence geometry.

Representative pattern:

```text
p ∣ n-u
q ∣ n+u
```

Determine:

1. the unique residue modulo `p*q` supplied by CRT;
2. whether the symmetric orientation gives a distinct residue;
3. how many residues survive after primitive/parity normalization;
4. whether endpoint-equals-prime exceptions change proper obstruction occupancy;
5. whether a product modulus `p*q` larger than the primitive interval gives an injective/at-most-one occupancy statement;
6. whether this is genuinely stronger than the existing `goldbach_primeWorld_crt` / residue periodicity statements.

Do not claim product-wave progress merely because CRT produces a residue. The key is whether the primitive restrictions yield a new injection, spacing, or localization estimate in the **actual short interval**.

Create and commit:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-004.md
```

---

## 8. Phase QP-005 — information-gain audit

This phase is mandatory even if all earlier facts are true.

Compare the original Goldbach finite fiber with the primitive/parity fiber quantitatively and formally where possible.

Questions:

- How many candidate offsets are removed by `Coprime n u`?
- How many obstruction primes/residue classes disappear at the same time?
- Does the local survivor density improve, stay equal, or worsen?
- Is any proposed primitive capacity inequality strictly stronger than the existing `GoldbachCapacityEscape` criterion?
- Can the primitive criterion be proved equivalent to Strong Goldbach, making it only a normalization?
- Does LR product-wave separation yield a theorem not derivable from the existing full prime-world CRT cardinality?
- Is there a new monotone quantity, injection, spacing bound, or collision constraint that survives normalization?

If the conclusion is "beautiful normalization, no strict information gain", record that explicitly as a successful Outcome B.

Create and commit:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-005.md
```

This report must contain the final classification, but it must refer back to the earlier committed reports rather than replacing them.

---

## 9. Outcome classification

Use exactly one primary outcome, with optional secondary notes.

### Outcome A — strict information gain

At least one kernel-checked theorem yields a genuinely stronger finite restriction than the existing Goldbach capacity/CRT ledger, such as a new injection, spacing bound, collision bound, short-fiber localization, or strict capacity improvement.

### Outcome B — structural normalization only

Primitive/parity/boundary theorems are correct and useful, but after exact accounting they are equivalent to or contained in the existing CRT/capacity framework. This is still valuable as a canonical quadratic layer.

### Outcome C — proposed route breaks

A central expected theorem is false. Supply a minimal Lean or numerical counterexample and identify the failed assumption.

### Outcome D — unexpected stronger route

The investigation discovers a different theorem or invariant that is not the planned primitive/overlap route and appears strictly stronger. It must still be kernel-checked or clearly marked as conjectural.

Do not label an outcome A/D merely because the reformulation is elegant.

---

## 10. Required scratch Lean deliverable

Create:

```text
DkMathTest/NumberTheory/GoldbachQuadraticPrimitiveAstra.lean
```

This file is a **research scratch target**. It must not be imported by the production Goldbach facade.

Requirements:

- import current production Goldbach modules and canonical `DkMath.Lib` GTail boundary modules;
- contain all proved candidate lemmas used in the reports;
- include concrete regression examples for important edge cases and discovered counterexamples;
- no `sorry`, `admit`, user `axiom`, or `unsafe`;
- prefer kernel-checkable `decide` for small finite examples when appropriate;
- do not use numerical testing as a substitute for proof of a universal lemma;
- use clear docstrings separating production facts from scratch hypotheses/observers.

If a candidate theorem is false, do not leave a failed theorem statement commented out without explanation. Encode a concrete counterexample theorem/example where practical and document it in the corresponding report.

Required focused verification:

```bash
cd lean/dk_math
lake build DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra
```

Also replay at least:

```bash
lake build DkMath.NumberTheory.Goldbach \
  DkMathTest.NumberTheory.GoldbachGNFiber
```

---

## 11. Required Python numerical deliverable

Create:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/goldbach_quadratic_primitive.py
```

Use deterministic standard Python where practical. External packages are optional but not required.

The script must be reproducible from the command line and should compute, for a configurable range of centers:

```text
all admissible offsets
positive offsets
primitive offsets gcd(n,u)=1
primitive parity-compatible offsets
actual Goldbach prime-pair offsets
raw left/right obstruction support
proper left/right obstruction support
support intersection sizes
LL / LR / RR local pair counts
original covered/survivor counts
primitive covered/survivor counts
endpoint-exception counts
```

Also search for:

- smallest failure of each proposed invariant;
- smallest positive higher-overlap example inside the primitive fiber;
- centers with worst primitive survivor density;
- centers where normalization changes capacity the least / most;
- possible strict spacing or at-most-one product-wave patterns.

The script must print a concise summary and be capable of writing machine-readable CSV or JSON output for selected diagnostics.

Save at least one representative output snapshot under:

```text
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/
```

Do not infer a universal theorem from finite computation.

---

## 12. Incremental reporting discipline

This is mandatory.

Do **not** work silently for the full session and then provide only a final result.

At each major phase:

1. write the corresponding `report-00N.md`;
2. include theorem names / counterexamples / numerical findings available at that point;
3. record build/test commands actually run;
4. commit the report and associated scratch changes;
5. only then continue to the next phase.

Reports are append-only research history. Later reports may correct earlier hypotheses, but must not erase the earlier decision trail.

If the investigation changes direction, add a new report explaining why before following the new branch.

The final response to the user should summarize the reports, not replace them.

---

## 13. Repository modification boundary

This task is research-only.

Allowed changes:

```text
DkMathTest/NumberTheory/GoldbachQuadraticPrimitiveAstra.lean
docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/**
```

Do not modify production files under:

```text
DkMath/NumberTheory/Goldbach/**
DkMath/Lib/**
```

unless an unavoidable build defect in the existing code is discovered. If that occurs, stop and document it rather than silently fixing production code.

Do not open a PR or merge this research branch.

---

## 14. Research guardrails

- Strong Goldbach is unproved unless a complete unconditional proof is actually kernel-checked; no renaming of an equivalent provider counts as proof.
- `GoldbachCapacityEscape` is already equivalent to Strong Goldbach. Do not reintroduce it under another name and classify that as information gain.
- Full-period CRT survival is already known and does not imply short-fiber survival.
- Raw divisibility is periodic; proper obstruction has endpoint exceptions. Keep them separate.
- Aesthetic similarity to primitive Pythagorean parametrization is motivation, not evidence.
- Shared use of Pascal coefficients does not imply GTail and Goldbach overlap are formally the same object.
- Prefer exact identities and injections before asymptotic or heuristic estimates.
- If a theorem can be proved without prime hypotheses, record the stronger general form.
- Search existing DkMath/Mathlib before implementing a duplicate theorem.

---

## 15. Final requested deliverables

At the end of the research session the branch must contain:

```text
instruction-000.md
report-000.md
report-001.md
report-002.md
report-003.md
report-004.md
report-005.md
DkMathTest/NumberTheory/GoldbachQuadraticPrimitiveAstra.lean
numeric/goldbach_quadratic_primitive.py
numeric/<representative output snapshot>
```

Additional reports are welcome if the reasoning branches materially.

The final user-facing answer should state only the high-level verdict after all artifacts are committed, and point to the reports. The mathematical reasoning trail, failed candidates, Lean scratch proofs, and numeric evidence must remain in the repository rather than existing only in chat output.
