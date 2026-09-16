# GTail Core Promotion — Goldbach/Pascal Addendum

Date: 2026-09-10  
Status: research / refactor addendum  
Base note: `analysis-001.md`  
Branch at time of writing: `develop`

## 0. Why this addendum exists

`analysis-001.md` was written before the Goldbach GN-fiber branch was completed and
merged into `develop`.

The Goldbach work independently produced a finite Pascal hierarchy inside obstruction
overlap accounting.  This does not prove a formal GTail/Goldbach equivalence, but it
supplies a new downstream consumer and new evidence for promoting Pascal / tail-depth
structure into the canonical `DkMath.Lib.*` layer.

This addendum does **not** replace or rewrite `analysis-001.md`.  Read both documents.
The original note remains the historical design analysis; this file records the new
post-Goldbach evidence and adjusts implementation priorities.

---

## 1. New develop-side evidence from Goldbach

Current public modules:

```text
DkMath.NumberTheory.Goldbach.Overlap
DkMath.NumberTheory.Goldbach.PairOverlap
```

The fixed-center obstruction support is:

```lean
goldbachObstructionSupport (n u : ℕ) : Finset ℕ
```

and its local `r`-fold multiplicity is now exposed as:

```lean
goldbachOffsetROverlapMultiplicity (n u r : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupport n u).card r
```

Therefore every offset with support cardinality `k` carries the local Pascal row

$$
r \longmapsto \binom{k}{r}.
$$

The `r = 2` layer is the unordered obstruction-pair ledger.

The branch also proved the exact local Pascal decomposition

$$
\binom{k}{2}=(k-1)+\binom{k-1}{2},
$$

and the exact global theorem

```lean
goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual
```

corresponding to

$$
\boxed{
\operatorname{PrimePairOverlapCount}=\operatorname{OverlapExcess}+\operatorname{PairOverlapResidual}.
}
$$

A kernel regression at `n = 35, u = 5` has support `{2,3,5}`, cardinality `3`,
and positive local residual `1`.  Thus the higher residual is not only a formal
definition; higher obstruction multiplicity occurs in the implemented finite model.

---

## 2. What this does and does not say about GTail

The structural analogy is now stronger:

```text
Goldbach obstruction support
    ↓ support.card = k
Pascal row choose(k,r)
    ↓
r-fold overlap layers

GTail(d,r)
    ↓
boundary coefficient choose(d,r)
    ↓
tail-depth / boundary layers
```

However, **no formal equivalence is currently proved** between
`goldbachOffsetROverlapMultiplicity` and `GTail`.

Do not introduce such an equivalence merely because both use `Nat.choose`.

In particular:

- Goldbach `r` counts subsets of a finite obstruction support.
- GTail `r` indexes a binomial higher-tail decomposition in the power-difference kernel.
- The common structure is Pascal recursion / filtration, not yet a proved identification
  of the underlying objects.

The refactor should first make the generic Pascal / GTail theorem surface canonical.
Only after that should Goldbach be revisited as a downstream consumer.

---

## 3. Dependency rule

Goldbach is a **consumer**, never a dependency of the core.

Allowed direction:

```text
DkMath.Lib.Cosmic.GTail*
DkMath.Lib.* Pascal / NumberTheory helpers
        ↓
DkMath.NumberTheory.Goldbach.*
```

Forbidden direction:

```text
DkMath.Lib.*
        ↓
DkMath.NumberTheory.Goldbach.*
```

Do not move Goldbach-specific obstruction definitions, endpoint exceptions, or
capacity ledgers into `DkMath.Lib.*`.

If a theorem discovered in Goldbach is genuinely generic, extract only the generic
finite-combinatorial statement, with no Goldbach vocabulary in the lower module.

---

## 4. Revised implementation priority

The original `analysis-001.md` listed:

```text
GTCORE-000 inventory
GTCORE-001 dependency inversion
GTCORE-002 exact boundary gcd
GTCORE-003 tail filtration
...
```

After the Goldbach work, the following order is recommended for the first implementation
passes:

### GTCORE-000 — inventory

Still first.  In addition to the original inventory, include:

- `Nat.choose` / Pascal recursion helpers duplicated in research modules;
- uses of `GTail_rec`;
- ad-hoc `r = 1` or `r = 2` decompositions that are candidates for a generic theorem;
- the new Goldbach Pascal observer as a downstream-consumer entry, not a migration target.

### GTCORE-003 — tail filtration / Pascal surface

Promote the `r → s` transport theorem early.

The goal is to make

$$
GTail(d,0) \to GTail(d,1) \to \cdots \to GTail(d,d)
$$

an explicit filtration with stable theorem names.

Also audit whether a small `GTailPascal` surface should package the boundary coefficient
and standard Pascal recursion facts used by higher-tail arguments.

### GTCORE-002 — exact boundary gcd

Once the boundary / filtration API is stable, locate or prove the generic boundary gcd
theorem proposed in `analysis-001.md`.

### GTCORE-001 — dependency inversion

Move generic `padicValNat` support out of ABC before expanding the valuation layer further.
This remains mandatory before `GTailPadic` can be considered architecturally canonical.

### GTCORE-004 onward

Then continue with prime-row higher-tail boundary, cyclotomic bridge, compatibility wrappers,
deprecations, and cross-project replay.

This ordering is a recommendation, not a theorem dependency requirement.  Codex may retain
the original ordering if repository constraints make dependency inversion necessary earlier,
but it should explain why.

---

## 5. Do not deprecate during inventory

The first Codex pass should be conservative.

During GTCORE-000:

- do not add `@[deprecated]`;
- do not globally rename GN references;
- do not rewrite FLT3 / FLT5 / ABC / RH / Goldbach consumers;
- do not change theorem statements merely to normalize naming;
- do not move files solely to match the proposed module diagram.

First produce the evidence table:

```text
current declaration
current module
semantic role
generic or project-specific
existing canonical replacement?
proposed canonical owner
downstream users
migration risk
```

Only after that table exists should implementation begin.

---

## 6. Additional cross-project replay target

The acceptance criteria in `analysis-001.md` should now include Goldbach.

At minimum, after any canonical GTail theorem / compatibility change, replay:

```text
DkMath.NumberTheory.Goldbach
DkMathTest.NumberTheory.GoldbachGNFiber
```

in addition to the existing FLT3 / FLT5 / ABC / Primitive / Pascal / RH targets.

Goldbach is useful as a regression consumer because it now contains both:

- legacy `GN 2` usage in the fixed-center fiber;
- a separate `Nat.choose` Pascal hierarchy that must **not** be accidentally conflated
  with GTail by refactoring.

---

## 7. Candidate generic extraction suggested by Goldbach

The Goldbach file currently proves a private arithmetic identity equivalent to

$$
\binom{k}{2} = (k-1)+\binom{k-1}{2}.
$$

Do not automatically promote this exact private theorem merely because it is generic.

During inventory, instead ask:

1. Does Mathlib already expose the needed Pascal recurrence in a form sufficient for all users?
2. Is there an existing DkMath Pascal helper module with the same theorem?
3. Would a generic theorem for arbitrary `r` be more canonical than a special `r = 2`
   identity?
4. Is the theorem genuinely part of GTail core, or only a generic combinatorial utility?

Avoid creating `DkMath.Lib.Cosmic.GTail*` theorems whose statements do not mention GTail
and belong more naturally in a Pascal / finite-combinatorics layer.

---

## 8. Important conceptual guardrail

The refactor is not a proof by analogy.

The repository now contains several structures that expose Pascal coefficients:

- GTail boundary heads;
- prime-row Pascal divisibility;
- Goldbach obstruction-overlap multiplicities.

This is evidence for a shared reusable API, but not proof that all three are manifestations
of one stronger theorem.

Codex should distinguish:

```text
proved common algebra
vs.
shared Nat.choose combinatorics
vs.
research-level structural analogy
```

in code, docstrings, and reports.

---

## 9. Suggested first Codex deliverable

Before theorem promotion, create a new inventory/report under this directory, for example:

```text
inventory-000.md
```

It should include:

1. all `[GNZC]` sites;
2. all `GN` definitions / abbrevs / wrappers;
3. all `cosmic_id_csr*` references;
4. all public `GTail*` declarations;
5. upward dependency violations from `DkMath.Lib.*`;
6. duplicated gcd / congruence / valuation / Pascal lemmas;
7. downstream consumers grouped by FLT3, FLT5, ABC, Primitive/Pascal, RH/CFBRC, Goldbach;
8. proposed migration class A/B/C/D from `analysis-001.md`;
9. candidate generic theorems that should exist before any deprecation;
10. baseline focused-build targets and current results.

The inventory should be factual.  If a candidate theorem is not found, report it as absent;
do not silently create a replacement during the inventory pass.

---

## 10. Updated research statement

The Goldbach merge adds a new independent observation:

> finite obstruction multiplicity naturally forms a Pascal hierarchy, and exact overlap
> accounting already uses its `r = 2` layer.

This strengthens the case that Pascal-depth structure should be a first-class reusable
surface near the GTail core.

It does **not** establish that Goldbach overlap is itself GTail.

The immediate refactor goal remains:

> make GTail the canonical power-difference boundary kernel, expose its Pascal filtration
> cleanly, repair core dependency direction, and leave project-specific arithmetic
> as downstream consumers.

After that refactor, Goldbach may resume with product-wave / CRT / short-fiber localization
and evaluate whether the canonical Pascal/GTail APIs provide a useful higher-overlap language.
