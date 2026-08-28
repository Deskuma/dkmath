# Codex autonomous implementation directive — Structural Arithmetic / Red Ribbon

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Primary integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration as an **autonomous Lean implementation task**.

Do not treat this document as a fixed patch recipe.  Treat the repository and a successful Lean build as the source of truth.  First inspect the current implementation, infer the strongest load-bearing next step, then implement it completely enough to become a reusable library checkpoint.

The overall mathematical objective is to unify, without conflating, the following DkMath ideas:

- KUS structural preservation `(K, U, S_U)`;
- the Red Ribbon interpretation of a chosen base/unit label;
- ordinary prime-factor / valuation coordinates;
- DHNT-style dynamic scaling;
- congruence / quotient / gauge-period observation;
- primitive multiplicative directions and finite-prime escape;
- generic Cosmic Formula `GN`;
- FLT5 `GN5` and golden-unit classification modulo fifth powers.

The key architectural principle is:

```text
KUS / raw source preserves structure.
StructuralArithmetic projects / forgets selected periodic information.
```

Do not replace KUS.  Do not redefine completed GN/FLT5 machinery.  Build bridges around existing proven APIs.

---

## 1. Repository-first preflight — mandatory before editing

Start by determining the actual repository state.  Do **not** assume that the phase labels in older documents are current.

At minimum inspect:

```bash
git status -sb
git branch --show-current
git rev-parse HEAD
git log --oneline --decorate -20
git merge-base HEAD develop
git diff --stat develop...HEAD
```

If the working tree contains unrelated user changes, do not overwrite, reset, stash, or stage them.  Work only in the Structural Arithmetic scope unless a directly required dependency must be changed.

Read the current versions of:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/PowerGauge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimeCoordinates.lean
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

Then search the repository before inventing any API:

```bash
rg -n "projectExponent|projectCoordinates|SamePowerSector|SamePowerStructure|projectPrimeCoordinates" DkMath
rg -n "InterPeriod|interPeriod|mod_mod|mod.*dvd|SamePowerStructure" DkMath
rg -n "GKUS|ScaleSpec|HarmonizeSpec|DecodeSpec|scaleUS|scaleGKUS|Transport" DkMath/KUS
rg -n "padicValNat_pow|factorization|PrimitivePrimeFactor|FreshPrimeFactor|exists_fresh_prime_factor" DkMath
rg -n "GoldenUnitClassesModFifth|signedGoldenFiniteUnitSectorCore|goldenUnitFifthClass" DkMath
rg -n "def GN|abbrev GN|GN5|primitive_prime_dvd_GN" DkMath
```

Inspect the definitions you actually plan to reuse.  Do not rely only on search snippets.

Also inspect at least these existing areas before choosing the next bridge:

```text
DkMath/KUS/README.md
DkMath/KUS/Coeff.lean
DkMath/KUS/Scale.lean
DkMath/KUS/Transport.lean
DkMath/ABC/PadicValNat.lean
DkMath/NumberTheory/PrimitiveBeam.lean
DkMath/NumberTheory/PrimitiveSet/Basic.lean
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/FinitePrimeEscapeGN5.lean
DkMath/FLT/Five/GN5.lean
DkMath/CosmicFormula/CosmicFormulaBinom.lean and/or the current canonical `GN` home
```

For the golden-unit side, locate the actual current theorem declarations by name rather than assuming a historical file path.

### Known orientation snapshot — verify, do not trust blindly

At the time this directive was written:

- `develop` HEAD was `4472ce331a9ea01b2e8532efc75f4465c5eb6ea7`.
- `StructuralArithmetic/` contained only `PowerGauge.lean` and `PrimeCoordinates.lean`.
- `PowerGauge` implemented period projection, period-0 identity/raw behavior, period-1 collapse, and Red Ribbon invariance under adding `d * k`.
- `PrimeCoordinates` implemented prime valuation coordinates and the theorem that multiplication by a `d`-th power is invisible after period-`d` projection.
- the user reported the StructuralArithmetic build passing after commit `6c863f1003fdea140b46f77431fae761e7c37830` fixed Lean elaboration issues.
- the old integration README still described Phase B as future work even though Phase B had already been implemented.

If the repository has advanced, follow the repository, not this snapshot.

---

## 2. Re-establish the mathematical contracts before choosing work

Keep the following distinctions explicit in theorem names, comments, and types.

### 2.1 Algebraic identity vs gauge period

`1` is the ordinary multiplicative identity/basepoint label:

```text
x * 1 = x
```

A natural `d` used by `projectExponent d n = n % d` is a **gauge period**, not a ring or monoid identity.

Never describe `5` as the multiplicative identity of the ambient ring.  In a period-5 quotient, adding 5 to an exponent is observationally invisible; that is a congruence-period statement.

### 2.2 Boundary periods

Preserve the already established semantics:

```text
period 0 : raw / unprojected observation
period 1 : total collapse of exponent-sector information
```

Do not model the ordinary prime world as `mod 1`.

### 2.3 Degree vs projection period

The existing Cosmic Formula `GN` has a degree/exponent argument `d`.

StructuralArithmetic also has a projection/gauge period.

These may numerically coincide in applications such as exponent five, but they are conceptually different parameters.  Do not create an API that silently identifies them.

### 2.4 Scale vs rebase vs project

Keep three operations distinct:

```text
scale   : change magnitude while retaining structural direction
rebase  : change the support/unit/base used to encode a value
project : intentionally forget period information
```

Example: `30^k = 2^k 3^k 5^k` preserves the original prime-support direction under exponent scaling.  Re-expressing the same real value as `6^k' = 2^k' 3^k'` changes support and is therefore a rebase, not the same scale operation.

Do not call nonzero real factors such as `2^k` ring-theoretic real primes.

### 2.5 `PrimitiveSet` naming warning

Existing `DkMath.NumberTheory.PrimitiveSet` means an Erdős-style divisibility antichain.  It is **not** the new multiplicative generator/primitive-scale notion.

Do not overload or reuse `PrimitiveSet` for the new closure/generator layer.

---

## 3. Autonomous decision rule

After the preflight, identify the **next missing theorem-level bridge that carries the most structure with the least new machinery**.

Use the following priority order unless repository evidence shows that a higher item is already implemented or the abstraction would be wrong.

### Priority A — inter-period projection / coarsening

This is the preferred next checkpoint if still absent.

Mathematical contract:

If `m ∣ d`, then a period-`d` observation can be canonically forgotten down to period `m`:

```text
(n % d) % m = n % m
```

Lift this from one exponent coordinate to arbitrary coordinate structures and then to prime coordinates.

Candidate theorem shapes — names are suggestions, not requirements:

```lean
theorem projectExponent_project_of_dvd
    {m d n : ℕ} (hmd : m ∣ d) :
    projectExponent m (projectExponent d n) = projectExponent m n

theorem projectCoordinates_project_of_dvd
    {ι : Type*} {m d : ℕ} (hmd : m ∣ d) (v : ι → ℕ) :
    projectCoordinates m (projectCoordinates d v) = projectCoordinates m v

theorem SamePowerStructure.of_dvd
    {ι : Type*} {m d : ℕ} (hmd : m ∣ d)
    {v w : ι → ℕ} (h : SamePowerStructure d v w) :
    SamePowerStructure m v w
```

Then provide the prime-coordinate specialization if it adds real reuse value.

Search Mathlib for the canonical remainder theorem first.  Do not re-prove modular arithmetic with `omega` if an exact library theorem already exists.

Handle period `0` and `1` consistently with the existing semantics rather than excluding them merely to simplify a proof.  If a nonzero hypothesis is genuinely required by Mathlib, document why and prove the strongest clean theorem available.

Prefer a small module such as:

```text
DkMath.NumberTheory.StructuralArithmetic.InterPeriod
```

but inspect repository naming conventions before deciding.

### Priority B — KUS observation bridge

Do this after Priority A, or instead only if an inter-period layer already exists and is sound.

The objective is **not** to force arbitrary KUS blueprints to be prime factorizations.

A good bridge should retain a KUS/raw source and attach or derive a StructuralArithmetic observation through an explicit specification.  If necessary, introduce a small spec that says how a support/blueprint yields raw exponent coordinates, rather than pretending every KUS object intrinsically has prime coordinates.

Possible architecture:

```text
raw KUS support --observation spec--> raw coordinates --project d--> visible coordinates
```

If proving compatibility with `ScaleSpec`, require an explicit compatibility hypothesis/specification.  Do not assert that every KUS scale transport preserves prime coordinates.

The important theorem-level distinction is:

```text
KUS source/support is retained.
Projection is lossy.
```

Avoid building a large wrapper hierarchy unless multiple concrete theorems immediately need it.

### Priority C — primitive multiplicative direction / finite-prime escape

Proceed here only after the projection vocabulary is stable enough.

Investigate whether Mathlib `Submonoid.closure` or another existing API is the right basis for the known-scale multiplicative closure.

Desired conceptual results include:

```text
adjoining 1 does not enlarge multiplicative generation
fresh prime outside a finite prime generator set is outside the generated closure
finite-prime escape produces a genuinely new prime direction
```

Promote general results out of `DkMath.Hackathon` only when doing so creates a clean ordinary library API.  Preserve the hackathon certificate as a consumer/demo if appropriate.

Do not conflate this with Erdős `PrimitiveSet`.

### Priority D — GN / FLT5 / golden-unit bridges

Only after the structural kernel is stable, connect existing theorems rather than modifying the completed proof tower.

Targets to investigate:

- canonical generic `DkMath.CosmicFormula.GN`;
- specialized `DkMath.FLT.Five.GN5`;
- `PrimitiveBeam.primitive_prime_dvd_GN` or its current equivalent;
- golden-unit fifth-power sector classification.

The desired explanatory shape for the golden-unit bridge is:

```text
epsilon = representative * delta^5
```

where the fifth-power factor is invisible to the period-5 observation and the representative labels the visible sector.

Do not rewrite the FLT5 proof merely to fit new terminology.

---

## 4. Scope discipline / anti-maze rule

This branch is an integration branch, so uncontrolled horizontal expansion is a failure mode.

Implement **one coherent load-bearing checkpoint at a time**.

After each candidate milestone, ask:

1. What global concept did this theorem make precise?
2. Which existing DkMath module now consumes or can consume it?
3. Did we remove an ambiguity, or merely create another abstraction layer?
4. Is the next gap a mathematical theorem, a missing bridge, or only documentation?

If Priority A is missing, implement and build it first.  After it passes, re-evaluate before opening a large KUS/Primitive/GN sub-project.

A second small module in the same run is acceptable only if it is a direct specialization/bridge of the first and does not introduce a new research branch.

Do not create long sequences of placeholder files or numbered speculative modules.

---

## 5. Lean implementation rules

- No `sorry`.
- No new axioms.
- No `unsafe` workaround for mathematical statements.
- Prefer existing Mathlib/DkMath lemmas over duplicate proofs.
- Keep imports as narrow as practical.
- Keep public definitions simple and theorem-oriented.
- Use explicit namespaces when a local theorem name such as `symm`/`trans` can shadow `Eq.symm`/`Eq.trans`.
- Be conservative with `simp` when exact theorem names make the intended reduction clearer.
- Avoid broad refactors or namespace moves.
- Do not modify completed FLT5 proof modules unless a bridge cannot be expressed externally and the reason is demonstrated.
- If a theorem needs an assumption, determine whether it is mathematically necessary or only an artifact of the chosen API before adding it.
- Separate raw data from projected data in the API.  A projected residue should not masquerade as a recoverable source.

Before introducing a new structure/typeclass, check whether a plain definition plus theorems is sufficient.

---

## 6. Build / verification protocol

Before editing, establish that the current baseline still builds if reasonably possible:

```bash
cd lean/dk_math
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic
```

After implementation, build every changed/new module individually, then the aggregate:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.<NewModule>
lake build DkMath.NumberTheory.StructuralArithmetic
```

If you changed a bridge importing KUS/GN/FLT5, also build the narrowest affected public consumer.

Do not report success merely because a source file looks type-correct.  A Lean build is the arbiter.

If an unrelated pre-existing build failure blocks a broader build, isolate it: prove that the new/changed module itself builds, record the unrelated blocker precisely, and do not "fix" unrelated code opportunistically.

Run repository lint/style checks that are already standard for this area if discoverable and inexpensive.

---

## 7. Documentation update is part of the implementation

The existing integration README is stale relative to the current code.  Update it after the implementation.

At minimum:

- mark already completed Phase A and Phase B as completed/build-checked if that remains true;
- record the newly implemented checkpoint;
- update the next unresolved gap;
- keep the distinction between identity, gauge period, raw source, scale, rebase, and projection explicit;
- record exact module/theorem names rather than prose-only claims.

Also create or update a concise implementation report in the same docs directory containing:

```text
baseline inspected
files changed
new definitions/theorems
mathematical contract
build commands and results
remaining gap
```

Do not claim more generality than the theorem signatures actually provide.

---

## 8. Public aggregation

If a new StructuralArithmetic module is stable and build-checked, add it to:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
```

Inspect broader DkMath import policy before adding any root-level `DkMath.lean` import.  Do not expose experimental modules globally merely because they exist.

---

## 9. Commit / push policy for this task

Once the chosen checkpoint and its documentation build cleanly:

1. inspect `git diff` and `git status`;
2. stage only files belonging to this Structural Arithmetic checkpoint;
3. create a terse descriptive commit;
4. push the current working branch to `origin`.

Do not merge to `develop`.
Do not open a PR unless explicitly requested separately.
Do not force-push.
Do not rewrite unrelated history.

If unrelated local modifications are present, leave them untouched and exclude them from the commit.

---

## 10. Final report format

Return a compact but rigorous report with:

### Situation

- branch and HEAD used;
- baseline build result;
- what was already implemented before this run;
- what stale documentation or naming ambiguity was found.

### Reasoning

- candidate gaps considered;
- why the selected checkpoint was the most load-bearing next step;
- any tempting direction intentionally deferred and why.

### Implementation

- files changed/added;
- definitions and theorem names;
- exact mathematical meaning.

### Verification

- exact `lake build ...` commands;
- pass/fail results;
- any lint/axiom audit performed.

### Next gap

State exactly one primary unresolved gap for the next run, plus at most one secondary optional follow-up.

### Git

- commit SHA;
- pushed branch;
- confirmation that no merge/PR was performed.

---

## 11. Success criterion

This task succeeds when Codex does more than add code: it must leave the repository in a state where the next structural relationship is **mathematically named, theorem-level, build-checked, documented, and reusable**.

The expected near-term architecture is:

```text
raw structural source
       |
       +-- KUS preserve / transport
       |
       +-- prime valuation coordinates
       |
       +-- period-d PowerGauge projection
       |        |
       |        `-- canonical inter-period forgetting when divisibility permits
       |
       +-- primitive multiplicative directions / finite escape
       |
       `-- GN / FLT5 / golden-unit applications
```

Keep the raw source as the authoritative structure.  Treat quotient observations as deliberately lossy views.  Build bridges; do not collapse these layers into one overloaded notion of "unit" or "GN world".
